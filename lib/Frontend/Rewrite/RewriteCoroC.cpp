//===--- RewriteCoroC.cpp - Playground for the code rewriter
//---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Hacks and fun related to the code rewriter.
//
//===----------------------------------------------------------------------===//

#include "clang/Rewrite/Frontend/ASTConsumers.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Attr.h"
#include "clang/AST/ParentMap.h"
#include "clang/Basic/CharInfo.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/IdentifierTable.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Lexer.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Core/RewriteHelper.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
#include <iostream>
#include <sstream>
#include <memory>

using namespace clang;
using llvm::utostr;

namespace ict {
/// \brief Check if the given type is CoroC auto-reference types.
///        Now, only `__chan_t', `__task_t' and `__refcnt_t'.
static inline bool IsCoroCAutoRefType(QualType T) {
  const Type *Ty = T.getTypePtrOrNull();
  if (Ty != nullptr)
    return Ty->isCoroCReferenceType();
  return false;
}

/// \brief Determines whether the given Expr is convert from NULL.
static inline bool IsNullToReference(Expr *E, ASTContext &C) {
  ImplicitCastExpr *Cast = dyn_cast<ImplicitCastExpr>(E);
  if (Cast != nullptr) {
    return Cast->getSubExpr()->isNullPointerConstant(C, 
                                    Expr::NPC_ValueDependentIsNull);
  }
  return false;
}

/// \brief Determines whether the given Type is like `__refcnt_t<T>'.
static inline bool IsCoroCGeneralRefType(QualType T) {
  T = T.getCanonicalType();
  const BuiltinType *BTy = 
          T.getTypePtr()->getAs<BuiltinType>();
  return (BTy != nullptr) && BTy->isCoroCGeneralRefType();
}

/// \brief Check if the given Expr is a VarRefExpr and is the CoroC 
///        auto-reference type.
static bool IsCoroCAutoRefExpr(Expr *E, DeclRefExpr **DE = nullptr) {
  if (!IsCoroCAutoRefType(E->getType())) return false;

  //while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E))
  //  E = ICE->getSubExpr();
  E = E->IgnoreParenImpCasts();
  /* record this DeclRefExpr pointer!! */
  if (DeclRefExpr *D = dyn_cast<DeclRefExpr>(E)) {
    if (DE) *DE = D;
    return true;
  }
  
  return isa<MemberExpr>(E) || isa<ArraySubscriptExpr>(E);
}

/// \brief Find all the DeclRefExprs in the given expression
///        wich CoroC auto-reference types.
class CoroCAutoRefFinder
    : public RecursiveASTVisitor<CoroCAutoRefFinder> {
  bool found;
public:
  CoroCAutoRefFinder() : found(false) {}

  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (IsCoroCAutoRefType(E->getType())) {
      found = true;
      return false;
    }
    return true;
  }

  bool Found() { return found; }
}; 

/// \brief Convert a given QualType to a unique string
static inline std::string ConvertTypeToSubName(QualType Ty) {
  std::string name = Ty.getAsString();
  std::string::size_type pos = 0;

  // find all the ' '/'['/']' to '_',
  // e.g. 'struct AA' ==> 'struct_AA'
  //      'int A[10]' ==> 'int_A_10_'
  while ((pos = name.find_first_of(" []", pos)) != std::string::npos) {
    name[pos++] = '_';
  }
  
  // find all the '*' to 'P'
  pos = 0;
  while ((pos = name.find_first_of("*", pos)) != std::string::npos) {
    name[pos++] = 'p';
  }
  return name;
}

/// \breif Get the FieldDecls inside the given structure type
static void inline 
GetRefDeclsInside(QualType Ty, std::vector<FieldDecl*> &Decls) {
  if (!Ty->isStructureType()) return;

  const RecordType *RTy = Ty->getAsStructureType();
  assert(RTy != nullptr);
  RecordDecl *RD = RTy->getDecl();
  
  for (RecordDecl::field_iterator I = RD->field_begin();
       I != RD->field_end(); ++I) {
    if (IsCoroCAutoRefType((*I)->getType()))
      Decls.push_back(*I);
  }
}

/// \brief Get the runtime function name of the given channel operand
static void GetChanFuncname(Expr *RHS, unsigned Opc,
                            std::string &funcName, bool &usePtr, 
                            ASTContext *Ctx = nullptr, 
                            bool isAutoRef = false,
                            bool sel = false, bool nonBlock = false) {
  bool isNullExpr = isa<CoroCNullExpr>(RHS);
  funcName = sel ? "__CoroC_Select_" : "__CoroC_Chan_";

  // FIXME : use a better way to get if the address of the RHS expr
  // can be caluculated by the '&' operator.
  if (isNullExpr)
    usePtr = false;
  else if (Ctx != nullptr)
    usePtr = (RHS->isModifiableLvalue(*Ctx, nullptr) == Expr::MLV_Valid);
  else
    usePtr = false;

  if (Opc == BO_Shr) {
    funcName += "Recv"; 
    if (isAutoRef) { 
      funcName += "Ref";
      usePtr = true;
    }
  } else {
    funcName += "Send";
    if (isAutoRef && usePtr)
      funcName += "Ref";
    else if (!isNullExpr && !usePtr)
      funcName += "Expr";
  }

  if (nonBlock)
    funcName += "_NB";

  return;
}

/// \brief The helper class to print the Expr with `__refcnt_t' var inside.
class CoroCStmtPrinterHelper : public PrinterHelper {
  PrintingPolicy Policy;
public:
  CoroCStmtPrinterHelper(const LangOptions& LangOpts)
    : Policy(LangOpts) { }
  virtual ~CoroCStmtPrinterHelper() {}
  
  virtual bool handledStmt(Stmt* E, llvm::raw_ostream& OS) {
    if (isa<MemberExpr>(E)) {
      return handledMemberExpr(dyn_cast<MemberExpr>(E), OS);
    } 
    if (isa<UnaryOperator>(E)) {
      return handledUnaryOperator(dyn_cast<UnaryOperator>(E), OS);
    }
    if (isa<BinaryOperator>(E)) {
      return handledBinaryOperator(dyn_cast<BinaryOperator>(E), OS);
    }
    if (isa<ArraySubscriptExpr>(E)) {
      return handledArraySubscriptExpr(dyn_cast<ArraySubscriptExpr>(E), OS);
    }
    // TODO: More cases to handle?
    return false;
  }

private:
  bool handledMemberExpr(MemberExpr *, llvm::raw_ostream&);
  bool handledUnaryOperator(UnaryOperator *, llvm::raw_ostream&);
  bool handledBinaryOperator(BinaryOperator *, llvm::raw_ostream&);
  bool handledArraySubscriptExpr(ArraySubscriptExpr *, llvm::raw_ostream&);
};

/// \brief Fixup stub for the GotoStmt when the dest label not found yet.
struct Fixup {
  LabelDecl *LD;
  SourceRange SR;
  RewriteHelper RH;

  Fixup(LabelDecl *_LD, SourceRange &_SR, Rewriter *Rewrite) 
    : LD(_LD), SR(_SR), RH(Rewrite) {
    RH << "{" << Endl; 
  }
};

/// \brief Thunk helper function for Spawn Operator
class ThunkHelper {
  ASTContext *Context;
  Rewriter &Rewrite;

  CallExpr *TheCallExpr;
  std::string ThunkUID;
  bool isGroupOp;
  bool isAsyncCall; // if used by __CoroC_Async_Call
  bool hasDump;
  bool useFuncPtr;

  void dumpThunkStruct(RewriteHelper &RH);
  void dumpThunkFuncArgsType(RewriteHelper &RH, const FunctionProtoType *FuncTy);
  void dumpThunkFunc(RewriteHelper &RH);

public:
  ThunkHelper(ASTContext *C, Rewriter &R, 
              CallExpr *CE, std::string UID, 
              bool isGrpOp = false, 
              bool isAsync = false)
      : Context(C), Rewrite(R), TheCallExpr(CE)
      , ThunkUID(UID), isGroupOp(isGrpOp)
      , isAsyncCall(isAsync)
      , hasDump(false), useFuncPtr(true) {
  }

  bool MatchCallExpr(CallExpr*, bool, bool);

  void DumpThunkCallPrologue(RewriteHelper &RH, CallExpr *CE,
                             DeclRefExpr *G, std::string paramName);

  void GetFuncName(std::string&);
  void GetCleanupName(std::string&);
  void GetStructName(std::string&);

  bool HasDump() { return hasDump; }

  void Dump(RewriteHelper &RH) {
    if (!hasDump) {
      RH << "\n/// auto generated by CoroC rewriter." << Endl;
      dumpThunkStruct(RH);
      dumpThunkFunc(RH);
      RH << "\n/// end\n" << Endl;
      hasDump = true;
    }
  }
};

/// \brief Select Helper for generating the code for '__CoroC_Select'
class SelectHelper {
  ASTContext *Context;
  Rewriter &Rewrite;
  long SelUID;
  SourceLocation StartLoc, EndLoc;

  unsigned CaseNum;
  unsigned CurPos;

  bool HasDefault;
  bool SimpleWay;

  RewriteHelper Prologue;
  std::stringstream Epilogue;
  std::map<unsigned, Expr*> AutoRefMap;
  std::vector<CoroCCaseStmt*> CaseStmtSet; 

  void dumpCleanupCode(SourceLocation Loc, unsigned pos) {
    bool generated = false;
    RewriteHelper RH(&Rewrite);

    std::map<unsigned, Expr*>::iterator It;

    if (pos == CaseNum) RH << " else {";
    RH << Endl;

    for (It = AutoRefMap.begin(); It != AutoRefMap.end(); ++It) {
      if (It->first != pos) {
        generated = true;
        RH << Indentation << "__refcnt_put(" 
           << It->second << ");" << Endl;
      }
    }

    if (!SimpleWay) {
      // Generate dealloc set code for each case stmt!!
      generated = true;
      RH << Indentation << Epilogue.str() << Endl;
    }
    
    if (generated) {
      if (pos == CaseNum) RH << "}"/* << Endl*/;
      RH.InsertTextAfterToken(Loc);
    }
  }

public:
  SelectHelper(ASTContext *Ctx, Rewriter &R, long UID, SourceLocation SL,
               SourceLocation EL, unsigned Num, bool hasDef)
      : Context(Ctx), Rewrite(R), SelUID(UID), StartLoc(SL), EndLoc(EL),
        CaseNum(Num), CurPos(0), HasDefault(hasDef), SimpleWay(false),
        Prologue(&R) {
    if (CaseNum == 1 || (CaseNum == 2 && HasDefault))
      SimpleWay = true;
  }

  void DumpPrologueAndEpilogue() {
    if (!SimpleWay) {
      Prologue << Indentation 
               << "__chan_t __select_result_" 
               << SelUID << " = __CoroC_Select(__select_set_" 
               << SelUID << ", " << !HasDefault << ");" << Endl;
    } 

    Prologue.InsertTextAfterToken(StartLoc);

    if (AutoRefMap.size() == 0 && SimpleWay) return;

    // generate the cleanup code for coroc auto references
    for (unsigned i = 0; i < CaseNum; ++i) {
      CompoundStmt *CS = dyn_cast<CompoundStmt>(CaseStmtSet[i]->getBody());
      assert(CS != nullptr && "the substmt of CoroCCaseStmt not a CompoundStmt");
      dumpCleanupCode(CS->getLocStart(), i);
    }

    if (!HasDefault) {
      CompoundStmt *CS = dyn_cast<CompoundStmt>(CaseStmtSet[CaseNum-1]->getBody());
      dumpCleanupCode(CS->getLocEnd(), CaseNum);
    }
  }

  void GenPrologueAndEpilogue() {
    Prologue << Endl;
    if (SimpleWay) return;

    int num = HasDefault ? CaseNum - 1 : CaseNum;
    Prologue << Indentation << "__select_set_t __select_set_" 
             << SelUID << " = __CoroC_Select_Alloc(" << num << ");" << Endl
             << Indentation << "__CoroC_Select_Init(__select_set_" << SelUID 
             << ", " << num << ");" << Endl; 
   
    Epilogue << "__CoroC_Select_Dealloc("
             << "__select_set_" << SelUID << ");";
  }

  void InsertCaseInitialization(BinaryOperator *BO) {
    std::string FuncName;
    Expr *RHS = BO->getRHS();
    bool UsePtr;
    bool IsAutoRef = IsCoroCAutoRefType(RHS->getType());

    GetChanFuncname(RHS, BO->getOpcode(), FuncName, UsePtr, 
                    Context, IsAutoRef, !SimpleWay, SimpleWay);

    // record the RHS if it'a coroc auto-ref and the oprand is channel send!!
    if (!SimpleWay && IsAutoRef && BO->getOpcode() == BO_Shl)
      AutoRefMap[CurPos] = RHS;

    if (SimpleWay)
      Prologue << Indentation << "_Bool __select_result_" 
               << SelUID << " = " << FuncName << "(";
    else
      Prologue << Indentation << FuncName 
               << "(__select_set_" << SelUID << ", ";

    Prologue << BO->getLHS() << ", ";

    if (UsePtr)
      Prologue << "&(" << BO->getRHS() << "));" << Endl;
    else
      Prologue << BO->getRHS() << ");" << Endl;
  }

  bool RewriteCaseStmt(CoroCCaseStmt *Case) {
    RewriteHelper RH(&Rewrite);

    CaseStmtSet.push_back(Case); // record this CoroCCaseStmt* !!

    if (CurPos == 0)
      RH << "if (";
    else
      RH << "else if (";

    SourceRange SR(Case->getLocStart());

    Expr *E = Case->getChanOpExpr();
    if (E != nullptr) {
      ParenExpr *PE = dyn_cast<ParenExpr>(E);
      assert(PE != nullptr);
      SR.setEnd(PE->getLocEnd());

      BinaryOperator *BO = reinterpret_cast<BinaryOperator *>(PE->getSubExpr());
      InsertCaseInitialization(BO);

      if (!SimpleWay)
        RH << "(" << BO->getLHS() << ") == ";

      RH << "__select_result_" << SelUID << ")";

    } else {
      RH << "!__select_result_" << SelUID << ")";
    }

    RH.ReplaceText(SR);

    return (++CurPos < CaseNum);
  }
};

class ScopeHelper;

/// \brief Recursive visit everything in AST, and make the translation.
class CoroCRecursiveASTVisitor
    : public RecursiveASTVisitor<CoroCRecursiveASTVisitor> {
  friend class ScopeHelper;

  static long unique_id_generator;

  Rewriter &Rewrite;
  ASTContext *Context;
  bool hasMain;
  bool isSingleReturnStmt;

  std::vector<ThunkHelper *> ThunkPool;
  std::vector<SelectHelper *> SelStk;

  std::vector<ScopeHelper *> ScopeStack;
  std::map<LabelDecl *, ScopeHelper *> LabelScopeMap;

  enum {
    NOT_INSERT = 0,
    NOT_PRINT_DECL = 1,
    NOT_PRINT_DEFINE = 2,
  };

  std::map<const Type*, unsigned> RefcntTypesMap;
  std::vector<const Type*> RefcntTypesCache;

  Token getNextTok(SourceLocation CurLoc);
  SourceLocation getNextTokLocStart(SourceLocation CurLoc);  

  ThunkHelper *getOrCreateThunkHelper(CallExpr *CE, bool isGroupOp, 
                                      bool isAsync = false);

  QualType getBaseRefType(QualType Ty);

  void rewriteCoroCRefTypeName(NamedDecl*, SourceLocation, 
                               QualType, bool isTypedef = false); 

  void pushSelStk(SelectHelper *Helper);
  SelectHelper *popSelStk();

  void emitCleanupUntil(RewriteHelper& RH,
                        unsigned Flags, SourceRange SR,
                        bool emitBlock = false,
                        ValueDecl *IgnoredVD = nullptr,
                        bool *IsLocal = nullptr);
  void emitCleanupUntil(unsigned Flags, SourceRange SR,
                        bool emitBlock = false,
                        ValueDecl *IgnoredVD = nullptr,
                        bool *IsLocal = nullptr);
  void emitCleanupWithLabel(LabelDecl *S, SourceRange SR);

  void AddDefaultInit(ValueDecl*, bool);

  void AddRefcntType(const Type*);

public:
  CoroCRecursiveASTVisitor(Rewriter &R, ASTContext *C)
      : Rewrite(R), Context(C), 
        hasMain(false), isSingleReturnStmt(false) { }

  ~CoroCRecursiveASTVisitor();

  void DumpThunkHelpers(RewriteHelper&);

  void DeclareRefcntTypes(RewriteHelper&);
  void DumpRefcntTypes(RewriteHelper&);

  void TraverseStmtWithoutScope(Stmt *S);

  bool VisitValueDecl(ValueDecl *D);
  bool VisitFunctionDecl(FunctionDecl *D);

  bool VisitTypedefNameDecl(TypedefNameDecl *D);

  bool VisitWhileStmt(WhileStmt *S);
  bool VisitForStmt(ForStmt *S);
  bool VisitDoStmt(DoStmt *S);
  bool VisitSwitchStmt(SwitchStmt *S);
  bool VisitCompoundStmt(CompoundStmt *S);

  bool VisitIfStmt(IfStmt *S);
  bool VisitLabelStmt(LabelStmt *S);
  bool VisitBreakStmt(BreakStmt *S);
  bool VisitContinueStmt(ContinueStmt *S);
  bool VisitGotoStmt(GotoStmt *S);
  bool VisitReturnStmt(ReturnStmt *S);

  bool VisitCoroCNewExpr(CoroCNewExpr *E);
  bool VisitCoroCSpawnCallExpr(CoroCSpawnCallExpr *E);
  bool VisitCoroCAsyncCallExpr(CoroCAsyncCallExpr *E);
  bool VisitCoroCMakeChanExpr(CoroCMakeChanExpr *E);
  bool VisitCoroCYieldStmt(CoroCYieldStmt *S);
  bool VisitCoroCQuitStmt(CoroCQuitStmt *S);

  bool VisitCoroCCaseStmt(CoroCCaseStmt *S);
  bool VisitCoroCSelectStmt(CoroCSelectStmt *S);

  bool VisitCallExpr(CallExpr *E);
  bool VisitMemberExpr(MemberExpr *E);
  bool VisitArraySubscriptExpr(ArraySubscriptExpr *E);

  Expr *VisitBinaryOperator(BinaryOperator *B);
  Expr *VisitChanOperator(BinaryOperator *B, unsigned Opc);
  Expr *VisitAssignmentOperator(BinaryOperator *B);
  Expr *VisitPtrMemIndirect(BinaryOperator *B);

  Expr *VisitUnaryOperator(UnaryOperator *U);
  Expr *VisitDerefOperator(UnaryOperator *U, bool isAutoDeref);

  bool HasMain() { return hasMain; }

  void PushScopeStack(ScopeHelper *Scope);
  void PopScopeStack();
  void InsertRefToCurScope(ValueDecl *VD);
  void EmitFixupCurScope(Fixup *fix);
  void EmitFixupEnd(Fixup *fix);

  void InsertLabelScope(LabelDecl *L);
  ScopeHelper *FindLabelScope(LabelDecl *L);

}; /* class CoroCRecursiveASTVisitor */

/// \brief
class RewriteCoroC : public ASTConsumer {
  DiagnosticsEngine &Diags;
  const LangOptions &LangOpts;
  ASTContext *Context;
  SourceManager *SM;
  std::string InFileName;
  raw_ostream *OutFile;
  CoroCRecursiveASTVisitor *Visitor;
  ScopeHelper *Global;

  Rewriter Rewrite;

public:
  void Initialize(ASTContext &context) override;

  // Top Level Driver code.
  bool HandleTopLevelDecl(DeclGroupRef D) override;
  
  void HandleTranslationUnit(ASTContext &C) override;

  RewriteCoroC(const std::string &inFile, raw_ostream *OS, DiagnosticsEngine &D,
               const LangOptions &LOpts);

  ~RewriteCoroC();
};

/// The bitmask for Scope Types.
enum {
  SCOPE_GLOBAL = 1,
  SCOPE_BLOCK = 2,
  SCOPE_LOOP = 4,
  SCOPE_FUNC = 8,
  SCOPE_FUNC_RET = 16,
};

/// \brief Hepler class for emulating the C scopes
class ScopeHelper {
  CoroCRecursiveASTVisitor *Visitor;

  std::vector<ValueDecl *> RefSet;
  std::vector<LabelDecl *> LabelSet;
  std::vector<Fixup *> FixupSet;

  void Exit() {
    // TODO: emit the global cleanups during the link stage.
    if (ScopeFlags & SCOPE_GLOBAL)
      return;

    // fixup each goto stmt in this scope,
    // if not clean, move them in the upper scope
    for (std::vector<Fixup *>::iterator I = FixupSet.begin();
         I != FixupSet.end(); ++I) {
      // emit the cleanup for current scope,
      // and move this stub to upper scope..
      Visitor->EmitFixupCurScope(*I);
    }

    // move to upper level of scope!
    Visitor->PopScopeStack();

    // move all the labels from current scope to the upper scope.
    for (std::vector<LabelDecl *>::iterator I = LabelSet.begin();
         I != LabelSet.end(); ++I) {
      Visitor->InsertLabelScope(*I);
    }
  }

  /// Emit the cleanup code for one given
  void EmitCleanupPerRef(RewriteHelper& RH, ValueDecl *VD,
                         std::string Prefix, bool emitBlock = true) {

    ASTContext *Ctx = Visitor->Context;
    QualType Ty = VD->getType();

    if (Ty->isStructureType()) {
      // for structures with chan_t / task_t fields inside!!
      Prefix += VD->getNameAsString();
      Prefix += ".";

      // get the RecordDecl of this structure!
      const RecordType *RTy = Ty->getAsStructureType();
      if (RTy == nullptr)
        return; // FIXME!

      RecordDecl *RD = RTy->getDecl();
      // for each field of this struct, call the EmitCleanupPerRef()
      // recurrently!
      for (RecordDecl::field_iterator I = RD->field_begin();
           I != RD->field_end(); ++I) {
        EmitCleanupPerRef(RH, *I, Prefix, emitBlock);
      }

    } else if (Ty->isArrayType()) {
      // FIXME : only support the 1-dimensional constant-sized array now!!
      if (!IsCoroCAutoRefType(Ctx->getBaseElementType(Ty)))
        return;
      const ConstantArrayType *ArrayTy = dyn_cast_or_null<ConstantArrayType>(
          Ctx->getAsArrayType(Ty)); // FIXME!
      if (ArrayTy == nullptr) 
        return; // FIXME

      if (emitBlock) RH << Indentation;
      RH << "__refcnt_put_array(" << Prefix 
         << VD << ", " << ArrayTy->getSize() << ");" << Endl;

    } else  {
      // ignore the var not with the special types.
      if (!IsCoroCAutoRefType(Ty))
        return;
      if (emitBlock) RH << Indentation;
      RH <<  "__refcnt_put(" << Prefix << VD << ");" << Endl;
    }
  }

public:
  SourceRange SR;
  unsigned ScopeFlags;

  ScopeHelper(CoroCRecursiveASTVisitor *_Visitor, SourceRange _SR,
              unsigned _Flags)
      : Visitor(_Visitor), SR(_SR), ScopeFlags(_Flags) {
    Visitor->PushScopeStack(this);
  }

  ~ScopeHelper() { Exit(); }

  /// Need or Not generate the cleanup code at the end of the compound scope.
  /// Now we'll ignore that if the scope is a function with a non-void return
  /// type.
  /// Because in that case, the block must be end with a 'return' stmt, and the
  /// cleanup code have been generated before the 'return' stmt yet!
  /// FIXME: some extra (useless) code may be generated in some other cases!!
  bool NeedGenBeforeExit() {
    return (RefSet.size() > 0) && !(ScopeFlags & SCOPE_FUNC_RET);
  }

  /// Return the total number of references defined in current scope.
  unsigned GetRefCnt() { return RefSet.size(); }

  /// If some goto stmt's destination label cannot be determined right now,
  /// we should create a FIXUP stub for it, and solve it after we know the
  /// label's info.
  void InsertFixup(Fixup *fix) { FixupSet.push_back(fix); }

  /// Insert a reference into these scope,
  /// TODO: By now, only `__chan_t' and `__task_t' will be treated as the
  /// auto-ptr,
  /// we'll add a generatic way to create auto-ptr for any kind of objects
  /// later.
  void InsertRef(ValueDecl *VD) { RefSet.push_back(VD); }

  /// Emit the cleanup code for each references defined in this scope,
  /// except the one who will be used as the return value (**IgnoredVD**).
  void EmitCleanup(RewriteHelper &RH, bool emitBlock = true,
                   ValueDecl *IgnoredVD = nullptr,
                   bool *IsLocal = nullptr) {
    // FIXME: special handlers need for struct and array!
    for (std::vector<ValueDecl *>::iterator I = RefSet.begin();
         I != RefSet.end(); ++I) {
      if (IgnoredVD == *I) {
        if (IsLocal) *IsLocal = true;
        continue;
      }
      EmitCleanupPerRef(RH, *I, "", emitBlock);
    }
  }

}; /* class ScopeHelper */

} /* namespace ict */

using namespace ict;

/// Overload this since the `->' operator of `__refcnt_t<T>'.
bool CoroCStmtPrinterHelper::handledMemberExpr(MemberExpr *Node,
                                               llvm::raw_ostream &OS) {
  Expr *BaseExpr = Node->getBase();
  if (BaseExpr->getType()->isCoroCGeneralRefType()) {
    // if the type of BaseExpr is `__refcnt_t', we must convert it
    //  ref->... => 
    //      (&((ref)->__obj[0]))->...
    OS << "(&((";
    BaseExpr->printPretty(OS, this, Policy);
    OS << ")->__obj[0]))";
  } else {
    BaseExpr->printPretty(OS, this, Policy);
  }
  
  /// The original code of StmtPrinter::VisitMemberExpr(..)
  MemberExpr *ParentMember = dyn_cast<MemberExpr>(Node->getBase());
  FieldDecl  *ParentDecl   = ParentMember
    ? dyn_cast<FieldDecl>(ParentMember->getMemberDecl()) : nullptr;

  if (!ParentDecl || !ParentDecl->isAnonymousStructOrUnion())
    OS << (Node->isArrow() ? "->" : ".");

  if (FieldDecl *FD = dyn_cast<FieldDecl>(Node->getMemberDecl()))
    if (FD->isAnonymousStructOrUnion())
      return true;

  if (NestedNameSpecifier *Qualifier = Node->getQualifier())
    Qualifier->print(OS, Policy);

  OS << Node->getMemberNameInfo();
  return true;
}

bool CoroCStmtPrinterHelper::handledArraySubscriptExpr(ArraySubscriptExpr *Node,
                                                       llvm::raw_ostream& OS) {
  Expr *BaseExpr = Node->getBase();
  if (!(BaseExpr->getType()->isCoroCGeneralRefType())) {
    return false;
  }

  // Convert ref[XX]  ==>
  //    (&((ref)->__obj[0]))[XX]

  OS << "(&((";
  BaseExpr->printPretty(OS, this, Policy);
  OS << ")->__obj[0]))";
  
  OS << "[";
  Node->getIdx()->printPretty(OS, this, Policy);
  OS << "]";
  return true;
}

bool CoroCStmtPrinterHelper::handledUnaryOperator(UnaryOperator *Node,
                                                  llvm::raw_ostream& OS) {
  Expr *SubExpr = Node->getSubExpr();
  unsigned opCode = Node->getOpcode();

  if (!(SubExpr->getType()->isCoroCGeneralRefType()) ||
      (opCode != UO_Deref && opCode != UO_AutoDeref)) {
    return false;
  }
  
  // Convert $ref =>
  //    (&((ref)->__obj[0]))
  // Convert *ref =>
  //    ((ref)->__obj[0])
  if (opCode == UO_AutoDeref) {
    QualType ElemType = Node->getType();
    assert(ElemType->isPointerType());
    OS << "(&";
  }

  OS << "(("; 
  SubExpr->printPretty(OS, this, Policy);
  OS << ")->__obj[0])";
  if (opCode == UO_AutoDeref) OS << ")";

  return true;
}

bool CoroCStmtPrinterHelper::handledBinaryOperator(BinaryOperator* Node, llvm::raw_ostream& OS) {
  unsigned opcode = Node->getOpcode();
  if (opcode != BO_Shl && opcode != BO_Shr) 
    return false;
  if (! Node->getLHS()->getType()->isCoroCChanRefType())
    return false;

  Expr *RHS = Node->getRHS();
  std::string FuncName;
  bool UsePtr = false;

  GetChanFuncname(RHS, opcode, FuncName, UsePtr, 
                  /*Context=*/nullptr, 
                  IsCoroCAutoRefType(RHS->getType())); 

  OS << FuncName.c_str() << "(";
  Node->getLHS()->printPretty(OS, this, Policy);
  OS << ", ";

  if (UsePtr) OS << "&(";

  RHS->printPretty(OS, this, Policy);
  
  if (UsePtr) OS << ")";
  
  OS << ")";

  return true;
}

/// Match if the current thunk is suitable for the given CallExpr
bool ThunkHelper::MatchCallExpr(CallExpr *CE, bool isGroupOp, bool isAsync) {
  if (!TheCallExpr || !CE)
    return false;
  // compare the two names, that methord works for C env
  return this->isGroupOp == isGroupOp &&
         this->isAsyncCall == isAsync &&
         (Rewrite.ConvertToString(TheCallExpr->getCallee()) ==
          Rewrite.ConvertToString(CE->getCallee()) );
}

/// Get the name of the thunk helper function
void ThunkHelper::GetFuncName(std::string &funcName) {
  funcName = "__thunk_helper_";
  funcName += ThunkUID;
}

void ThunkHelper::GetCleanupName(std::string &cleanupName) {
  cleanupName = "__thunk_cleanup_";
  cleanupName += ThunkUID;
}

/// Get the typename of the thunk helper's param
void ThunkHelper::GetStructName(std::string &structName) {
  structName = "__thunk_struct_";
  structName += ThunkUID;
}

/// Dump the thunk calling code into the OS
void ThunkHelper::DumpThunkCallPrologue(RewriteHelper &RH, CallExpr *CE,
                                        DeclRefExpr *G, std::string paramName) {
  // if the CE's callee is a global expr, directly call it!!
  // FIXME : this implementation is not good !!
  Expr *E = CE->getCallee();
  while (CastExpr *Cast = dyn_cast<CastExpr>(E)) {
    E = Cast->getSubExpr();
  }
  if (E != nullptr && isa<DeclRefExpr>(E)) {
    DeclRefExpr *DE = dyn_cast<DeclRefExpr>(E);
    assert(DE != nullptr);
    DeclContext *DC = DE->getDecl()->getDeclContext();
    if (DC == nullptr || isa<TranslationUnitDecl>(DC))
      useFuncPtr = false;
  }


  RH << Indentation << "struct __thunk_struct_" 
     << ThunkUID << "*  " << paramName << " = ("
     << "struct __thunk_struct_" << ThunkUID << "*)"
     << "malloc(sizeof(struct __thunk_struct_" 
     << ThunkUID << "));" << Endl;

  // Init each arg
  int i = 0;
  CallExpr::arg_iterator it = CE->arg_begin();
  for (; it != CE->arg_end(); ++it) {
    RH << Indentation << paramName << "->_param" << i++ << " = ";

    if (!isAsyncCall &&
        IsCoroCAutoRefType((*it)->getType()))
      RH << "__refcnt_get(" << *it << ");" << Endl;
    else
      RH << *it << ";" << Endl;
  }

  // Init the group tag if has one
  if (isGroupOp && G != nullptr)
    RH << Indentation << paramName 
       << "->_group = " << G << ";" << Endl;

  // Init the function pointer
  if (useFuncPtr)
    RH << Indentation << paramName << "->_fp = (void*)("
       << (Stmt*)(CE->getCallee()) << ");" << Endl << Indentation;

  // Inc the task number in the group
  if (isGroupOp && G != nullptr) {
    RH << Indentation 
       << "__CoroC_Add_Task(" << G << ");" << Endl;
  }
}


/// Dump the thunk param struct's body
void ThunkHelper::dumpThunkStruct(RewriteHelper& RH) {
  QualType Ty = TheCallExpr->getCallReturnType();

  RH << Endl << "struct __thunk_struct_" << ThunkUID << " { " << Endl;

  int i = 0;
  CallExpr::arg_iterator it = TheCallExpr->arg_begin();
  for (; it != TheCallExpr->arg_end(); ++it) {
    RH << Indentation << (*it)->getType() << " _param" << i++ << ";" << Endl;
  }
  
  if (isGroupOp)
    RH << Indentation << "__group_t _group;" << Endl;
  
  // FIXME : only be used by __CorC_Async_Call ..
  if (isAsyncCall && Ty != Context->VoidTy)
    RH << Indentation << Ty << " _ret;" << Endl;

  // FIXME : use a function pointer to reference the 
  // actually called function because the CallExpr may be
  // a local var such as function pointer or member field,
  // which cannot reference outside the local scope, so record
  // the function's address into the param structure now.
  if (useFuncPtr)
    RH << Indentation << "void *_fp;" << Endl;
  
  RH << "};" << Endl;
}

/// Dump the thunk function's arglist types
void ThunkHelper::dumpThunkFuncArgsType(RewriteHelper& RH,
                                        const FunctionProtoType *FuncTy) {

  unsigned numArgs = FuncTy->getNumParams();
  for (unsigned i = 0; i < numArgs; ++i) {
    RH << (FuncTy->getParamType(i));
    if (i < numArgs - 1) RH << ", ";
  }
}

/// Dump the thunk function defination
void ThunkHelper::dumpThunkFunc(RewriteHelper &RH) {
  unsigned numArgs = TheCallExpr->getNumArgs();
  Expr *E = TheCallExpr->getCallee();

  /// Generate the thunk func declaration:
  RH << Endl << "static "
     << (isAsyncCall ? "void" : "int")
     << " __thunk_helper_" << ThunkUID << "("
     << "struct __thunk_struct_" << ThunkUID << " *_arg) {" << Endl;

  // Generate the func body:

  if (useFuncPtr) {
    // 1.1. decalarate a pointer to the callee
    RH << Indentation << TheCallExpr->getType() << " (*fp) (";
  
    QualType T = E->getType();
    assert(T->isPointerType());

    const Type *Ty = T->getPointeeType()->getUnqualifiedDesugaredType();
    assert(isa<FunctionProtoType>(Ty));

    const FunctionProtoType *FuncTy =
      reinterpret_cast<const FunctionProtoType *>(Ty);

    dumpThunkFuncArgsType(RH, FuncTy);
 
    RH << ");" << Endl;

    // 1.2. assign the callee address to the `fp'
    RH << Indentation << "fp = (typeof(fp))(_arg->_fp);" << Endl;

    // 1.3. calling the thunk helper function
    if (!isAsyncCall ||
        TheCallExpr->getType() == Context->VoidTy)
      RH << Indentation << "fp(";
    else
      RH << Indentation << "_arg->_ret = fp(";
  } else {
    // directly calling the function 
    if (!isAsyncCall ||
        TheCallExpr->getType() == Context->VoidTy)
      RH << Indentation << E << "(";
    else
      RH << Indentation << "_arg->_ret = " << E << "(";
  }
  
  std::vector<int> ArgStk;
  if (numArgs > 0) {
    int i = 0;
    CallExpr::arg_iterator it = TheCallExpr->arg_begin();
    for (;;) {
      QualType Ty = (*it)->getType();
      if (IsCoroCAutoRefType(Ty))
        ArgStk.push_back(i);

      RH << "_arg->_param" << i++;
      if (++it == TheCallExpr->arg_end())
        break;
      RH << ", ";
    }
  }

  RH << ");" << Endl;

  if (isAsyncCall)
    RH << Indentation << "return;" << Endl;
  else
    RH << Indentation << "__CoroC_Exit(0);" << Endl;

  RH << "}" << Endl;
  
  if (isAsyncCall) return ;

  /// Generate the cleanup callback declaration:
  RH << Endl << "static int __thunk_cleanup_" << ThunkUID << "("
     << "struct __thunk_struct_" << ThunkUID << " *_arg, int _ret) {" << Endl;

  // Generate the func body:
  
  // 2.1. release the auto-references if any exisit
  for (unsigned k = 0; k < ArgStk.size(); ++k) {
    RH << Indentation << "__refcnt_put(_arg->_param" 
       << ArgStk[k] << ");" << Endl;
  }

  // 2.2. join to the given group
  if (isGroupOp)
    RH << Indentation 
       << "__CoroC_Notify(_arg->_group, _ret);" << Endl;

  // 2.3. release the _arg and quit
  RH << Indentation << "free(_arg);" << Endl;
 
  RH << Indentation << "return _ret;" << Endl;
  RH << "}" << Endl;
}

/// The static item of the CoroCRecursiveASTVisitor
long CoroCRecursiveASTVisitor::unique_id_generator = 0;

/// The destructor of the CoroCRecursiveASTVisitor
CoroCRecursiveASTVisitor::~CoroCRecursiveASTVisitor() {
  std::vector<ThunkHelper *>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it)
    delete (*it);
}

/// Get and return the next token after the one in current location
Token CoroCRecursiveASTVisitor::getNextTok(SourceLocation CurLoc) {
  int offset = Lexer::MeasureTokenLength(CurLoc, Rewrite.getSourceMgr(),
                                         Rewrite.getLangOpts());

  Token TheTok;
  assert(!Lexer::getRawToken(CurLoc.getLocWithOffset(offset), TheTok,
                             Rewrite.getSourceMgr(), Rewrite.getLangOpts(),
                             true));
  return TheTok;
}

/// Get the next token after the one in current location
/// and return the source location of that token.
SourceLocation
CoroCRecursiveASTVisitor::getNextTokLocStart(SourceLocation CurLoc) {
  Token TheTok = getNextTok(CurLoc);
  return TheTok.getLocation();
}

/// Dump all thunk helpers' code if neccessary..
void CoroCRecursiveASTVisitor::DumpThunkHelpers(RewriteHelper &RH) {
  std::vector<ThunkHelper *>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it)
    (*it)->Dump(RH);
}

void CoroCRecursiveASTVisitor::AddRefcntType(const Type *Ty) {
  if (!RefcntTypesMap[Ty]) {
    RefcntTypesCache.push_back(Ty);
    RefcntTypesMap[Ty] = NOT_PRINT_DECL;
  }
}

void CoroCRecursiveASTVisitor::DeclareRefcntTypes(RewriteHelper &RH) {
  std::vector<const Type *>::iterator it = RefcntTypesCache.begin();
  for (; it != RefcntTypesCache.end(); ++it) {
    const Type *ty = *it;
    // Make sure each declaration is printed only once!!
    if (RefcntTypesMap[ty] != NOT_PRINT_DECL) 
      continue;

    QualType QT = QualType(ty, 0);
    RH << "struct __refcnt_" << ConvertTypeToSubName(QT) << ";" << Endl;  
    RefcntTypesMap[ty] = NOT_PRINT_DEFINE;
  } 
}

void CoroCRecursiveASTVisitor::DumpRefcntTypes(RewriteHelper &RH) {
  std::vector<const Type *>::iterator it = RefcntTypesCache.begin();
  for (; it != RefcntTypesCache.end(); ++it) {
    const Type *ty = *it;
    QualType QT = QualType(ty, 0);

    bool isStructOrUnion = QT->isStructureType();

    // dump the type definition
    RH << "struct __refcnt_" << ConvertTypeToSubName(QT) << " {" << Endl;
    RH << Indentation << "struct tsc_refcnt __refcnt;" << Endl;

    if (isStructOrUnion) {
      RH << Indentation << "void (*__user_fini)(" << QT << "*);" << Endl; // FIXME
      RH << Indentation << "int __obj_num;" << Endl;
    }

    RH << Indentation << QT << " __obj[1];" << Endl;
    RH << "};" << Endl << Endl; 
    
    // we don't add user-defined destoctors for basic or builtin types.
    if (!isStructOrUnion) continue;

    // dump the destructor of the new generated type
    std::vector<FieldDecl*> Decls;
    GetRefDeclsInside(QT, Decls);

    RH << "static void __refcnt_" << ConvertTypeToSubName(QT) << "_fini("
       << "struct __refcnt_" << ConvertTypeToSubName(QT) << "* __arg) {" << Endl;
    
    if (Decls.size() > 0) {
      RH << Indentation << "int i;" << Endl
         << Indentation << "for (i=0; i<__arg->__obj_num; ++i) {" << Endl;
      for (unsigned i = 0; i < Decls.size(); ++i) {
        ValueDecl *VD = Decls[i];
        RH << Indentation << "  __refcnt_put(__arg->__obj[i]." << VD << ");" << Endl;
      }
      RH << Indentation << "}" << Endl;
    }

    // call the user defined fini ..
    RH << Indentation << "if (__arg->__user_fini)" << Endl
       << Indentation << "  __arg->__user_fini(&__arg->__obj[0]);" << Endl;

    // call the free to release the memory ..
    RH << Indentation << "free(__arg);" << Endl;

    RH << "}" << Endl << Endl;
  }
  RefcntTypesCache.clear();
}

/// Get or Create a thunk helper for CoroC Spawn Call
ThunkHelper *CoroCRecursiveASTVisitor::getOrCreateThunkHelper(CallExpr *C, 
                                                              bool isGroupOp,
                                                              bool isAsync) {
  std::vector<ThunkHelper *>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it) {
    if ((*it)->MatchCallExpr(C, isGroupOp, isAsync))
      return (*it);
  }

  std::stringstream SS;
  SS << unique_id_generator++;

  ThunkHelper *Thunk = new ThunkHelper(Context, Rewrite, 
                                       C, SS.str(), isGroupOp, isAsync);

  ThunkPool.push_back(Thunk);
  return Thunk;
}

/// Push / Pop the SelectHelper Stack
void CoroCRecursiveASTVisitor::pushSelStk(SelectHelper *Helper) {
  SelStk.push_back(Helper);
}

SelectHelper *CoroCRecursiveASTVisitor::popSelStk() {
  if (SelStk.empty())
    return nullptr;
  SelectHelper *SH = SelStk.back();
  SelStk.pop_back();
  return SH;
}

/// Push / Pop the ScopeHelper Stack
void CoroCRecursiveASTVisitor::PushScopeStack(ScopeHelper *Scope) {
  ScopeStack.push_back(Scope);
}

void CoroCRecursiveASTVisitor::PopScopeStack() {
  ScopeHelper *CurScope = ScopeStack[ScopeStack.size() - 1];
  if ((CurScope->ScopeFlags & SCOPE_GLOBAL) == 0 &&
      CurScope->NeedGenBeforeExit()) {
    // TODO: solve the global auto-references in the link stage!!
    RewriteHelper RH(&Rewrite);
    CurScope->EmitCleanup(RH, false);
    RH.InsertText(CurScope->SR.getEnd());
  }
  ScopeStack.pop_back();
}

void CoroCRecursiveASTVisitor::InsertRefToCurScope(ValueDecl *VD) {
  ScopeHelper *CurScope = ScopeStack[ScopeStack.size() - 1];
  CurScope->InsertRef(VD);
}

/// Fixup the GotoStmt for current scope level
void CoroCRecursiveASTVisitor::EmitFixupCurScope(Fixup *fix) {
  ScopeHelper *CurScope = ScopeStack[ScopeStack.size() - 1];
  ScopeHelper *NextScope = ScopeStack[ScopeStack.size() - 2];

  if (FindLabelScope((fix)->LD) == CurScope ||
          (NextScope->ScopeFlags & SCOPE_GLOBAL))
    // find the label for goto fixup stub,
    // so we should finish this fix and delete the stub now.
    return EmitFixupEnd(fix);

  CurScope->EmitCleanup(fix->RH, false);

  NextScope->InsertFixup(fix);
}

/// Finish the GotoStmt fixup stub, rewrite the code.
/// NOTE: this function will be called when the given Label
/// is defined in current scope or we reach the global scope.
/// (which means a goto statement's dest lable is not defined in
/// current function, this may causes undefined error, but must
/// be handled by the programmer himself!!)
void CoroCRecursiveASTVisitor::EmitFixupEnd(Fixup *fix) {
  RewriteHelper &RH = fix->RH;

  RH.InsertText(fix->SR.getBegin());
  RH << Endl << "}" << Endl;
  RH.InsertTextAfterToken(getNextTokLocStart(fix->SR.getEnd()));

  delete fix; // FIXME!!
}

/// Visit the CompoundStmt without the Scope info
void CoroCRecursiveASTVisitor::TraverseStmtWithoutScope(Stmt *S) {
  if (S == nullptr)
    return;

  CompoundStmt *CS = dyn_cast<CompoundStmt>(S);
  if (CS == nullptr) {
    TraverseStmt(S);
  } else {
    for (Stmt **It = CS->body_begin(); It != CS->body_end(); ++It) {
      isSingleReturnStmt = isa<ReturnStmt>(*It) || 
                           isa<CoroCQuitStmt>(*It) ||
                           isa<CallExpr>(*It);
      TraverseStmt(*It);
      isSingleReturnStmt = false;
    }
  }
#if 0
  // FIXME: Reset the children pointer to all nullptr,
  // so the children will not be traverse again!!
  for (Stmt::child_range range = S->children(); range; ++range) {
    *range = nullptr;
  }
#endif
}

/// The template method for all the loop stmts.
template <typename T>
bool VisitLoopStmt(CoroCRecursiveASTVisitor *Visitor, T *S) {
  ScopeHelper Scope(Visitor, S->getSourceRange(), SCOPE_LOOP);
  for (Stmt::child_range range = S->children(); range; ++range)
    Visitor->TraverseStmtWithoutScope(*range);
  return false;
}

/// Visit the ForStmt
bool CoroCRecursiveASTVisitor::VisitForStmt(ForStmt *S) {
  return VisitLoopStmt<ForStmt>(this, S);
}

/// Visit the WhileStmt
bool CoroCRecursiveASTVisitor::VisitWhileStmt(WhileStmt *S) {
  return VisitLoopStmt<WhileStmt>(this, S);
}

/// Visit the DoStmt
bool CoroCRecursiveASTVisitor::VisitDoStmt(DoStmt *S) {
#if 0
  return VisitLoopStmt<DoStmt>(this, S);
#else
  SourceRange Range(S->getLocStart(), S->getBody()->getLocEnd());
  ScopeHelper Scope(this, Range, SCOPE_LOOP);
  for (Stmt::child_range range = S->children(); range; ++range)
    TraverseStmtWithoutScope(*range);
  return false;
#endif
}

/// Visit the SwitchStmt
bool CoroCRecursiveASTVisitor::VisitSwitchStmt(SwitchStmt *S) {
  return VisitLoopStmt<SwitchStmt>(this, S);
}

/// Visit the CompoundStmt,
bool CoroCRecursiveASTVisitor::VisitCompoundStmt(CompoundStmt *S) {
  ScopeHelper Scope(this, S->getSourceRange(), SCOPE_BLOCK);
  TraverseStmtWithoutScope(S);
  return false;
}

/// Visit the FunctionDecl, change the `main' to `__CoroC_UserMain'
bool CoroCRecursiveASTVisitor::VisitFunctionDecl(FunctionDecl *D) {
  // rewrite the return type if it is a `__chan_t<T> ':
  QualType Ty = D->getReturnType();
  if (Ty->isPointerType())
    Ty = Ty.getTypePtr()->getPointeeType();

  SourceLocation StartLoc = D->getReturnTypeSourceRange().getBegin();
  rewriteCoroCRefTypeName(D, StartLoc, Ty);

  // for function decleration with a name :
  if (D->getDeclName()) {
    if (D->getNameAsString() == "main") {
      SourceLocation SL = D->getNameInfo().getLoc();
      Rewrite.ReplaceText(SL, 4, "__CoroC_UserMain");
      // if the params of `main' are ignored,
      // we must add the default ones.
      if (D->param_size() == 0) {
        SL = getNextTokLocStart(SL);
        Rewrite.InsertTextAfterToken(SL, "int __argc, char **__argv");
      }
      // if the `main' is just a declaration but not a defination,
      // we don't need to generate the wrapper call.
      hasMain = D->hasBody();
    }

    // if the function with a compound body,
    // we'll insert a new scope level for (arg0, arg1, ...) { ... }
    CompoundStmt *CS;
    if (D->hasBody() &&
        (CS = dyn_cast<CompoundStmt>(D->getBody())) != nullptr) {
      unsigned Flags = SCOPE_FUNC | SCOPE_BLOCK;
      if (D->getReturnType() != Context->VoidTy)
        Flags |= SCOPE_FUNC_RET;

      ScopeHelper Scope(this, CS->getSourceRange(), Flags);

      // NOTE: for C-style function calls, we do not care about the
      //       params which is auto-ptr, the caller will dec its counter;
      //       for CoroC Spawn calls, the wrapper calls will dec the counter,
      //       so in the function body, we don't need to add the params to
      //       scope.
      for (unsigned i = 0; i < D->param_size(); ++i)
        TraverseDecl(D->getParamDecl(i));

      TraverseStmtWithoutScope(D->getBody());
      return false;
    }
  }

  return true;
}

/// For rewrite the TypedefNameDecl if it include a `__chan_t<Type>'
bool CoroCRecursiveASTVisitor::VisitTypedefNameDecl(TypedefNameDecl *D) {
  QualType Ty = D->getUnderlyingType();
  QualType BaseTy = getBaseRefType(Ty);

  TypeSourceInfo *TS = D->getTypeSourceInfo();
  if (TS != nullptr)
    rewriteCoroCRefTypeName(D, TS->getTypeLoc().getLocStart(), BaseTy, true);
  
  return true;
}


/// For the [LableDecl* ==> ScopeHelper*] map's operantions:
void CoroCRecursiveASTVisitor::InsertLabelScope(LabelDecl *S) {
  ScopeHelper *CurScope = ScopeStack[ScopeStack.size() - 1];
  LabelScopeMap[S] = CurScope;
}

ScopeHelper *CoroCRecursiveASTVisitor::FindLabelScope(LabelDecl *S) {
  if (LabelScopeMap.find(S) == LabelScopeMap.end())
    return nullptr;
  return LabelScopeMap[S];
}

/// Emit the cleanup clauses until the given scope type
void CoroCRecursiveASTVisitor::emitCleanupUntil(RewriteHelper &RH,
                                                unsigned Flag, SourceRange SR,
                                                bool emitBlock, 
                                                ValueDecl *IgnoredVD, bool *IsLocal) {
  unsigned size = ScopeStack.size();
  bool output = false;
  ScopeHelper *Scope = ScopeStack[size - 1];

  if (emitBlock)
    RH << "{" << Endl;

  do {
    Scope = ScopeStack[--size];
    if (Scope->GetRefCnt() > 0) {
      Scope->EmitCleanup(RH, emitBlock, IgnoredVD, IsLocal);
      output = true;
    }
  } while (!(Scope->ScopeFlags & Flag));

  // if no cleanup clause is emited, just abort.
  if (!output)
    return;
  
  // if the single stmt and cleanup codes in 
  // one block scope, should add indentation before.
  if (emitBlock) RH << Indentation;

  // write the cleanups within a compound block
  RH.InsertText(SR.getBegin(), false);

  // find the ';' after the given statement, and insert a '}' after it.
  if (emitBlock) {
    RH << Endl << "}" << Endl;
    RH.InsertTextAfterToken(getNextTokLocStart(SR.getEnd()));
  }
 
}

void CoroCRecursiveASTVisitor::emitCleanupUntil(unsigned Flag, SourceRange SR,
                                                bool emitBlock, ValueDecl *IgnoredVD,
                                                bool *IsLocal) {
  RewriteHelper RH(&Rewrite);
  return emitCleanupUntil(RH, Flag, SR, emitBlock, IgnoredVD, IsLocal);
}

/// Emit the cleanup clauses for a goto statement with given label.
void CoroCRecursiveASTVisitor::emitCleanupWithLabel(LabelDecl *S,
                                                    SourceRange SR) {
  unsigned size = ScopeStack.size();
  bool output = false;
  ScopeHelper *CurScope = ScopeStack[--size];
  ScopeHelper *LabelScope = FindLabelScope(S);

  if (LabelScope == nullptr) {
    // gen a fixup stub for this goto statement
    Fixup *fix = new Fixup(S, SR, &Rewrite);
    CurScope->InsertFixup(fix);
    return;
  }

  // if the two scopes are the same, no cleanup need to be generated!
  if (LabelScope == CurScope || CurScope->GetRefCnt() == 0)
    return;

  // now, insert the cleanups for each scope until reach the Label's
  RewriteHelper RH(&Rewrite);
  RH << "{" << Endl;

  while (CurScope != LabelScope && size > 0) {
    if (CurScope->GetRefCnt() > 0) {
      CurScope->EmitCleanup(RH);
      output = true;
    }
    CurScope = ScopeStack[--size];
  }

  if (output) {
    RH << Indentation;
    RH.InsertText(SR.getBegin());

    RH << Endl << "}" << Endl;
    RH.InsertTextAfterToken(getNextTokLocStart(SR.getEnd()));
  }
}

/// Visit the IfStmt, ignore the children 's result
bool CoroCRecursiveASTVisitor::VisitIfStmt(IfStmt *S) {
  /// **BUG** !!
  ///    We have no method to continue traverse the other Stmt*
  ///    when one of its previous brother return with a false !!
  for (Stmt::child_range range = S->children(); range; ++range) {
    TraverseStmt(*range);
  }
  return false;
}


/// Visit the LabelStmt, record the label with current scope info.
bool CoroCRecursiveASTVisitor::VisitLabelStmt(LabelStmt *S) {
  InsertLabelScope(S->getDecl());
  return true;
}

/// Visit the BreakStmt, try to emit the cleanup clauses until finish the
/// current loop
bool CoroCRecursiveASTVisitor::VisitBreakStmt(BreakStmt *S) {
  emitCleanupUntil(SCOPE_LOOP, S->getSourceRange(), true);
  return true;
}

/// Visit the ContinueStmt, do the same works as BreakStmt
bool CoroCRecursiveASTVisitor::VisitContinueStmt(ContinueStmt *S) {
  emitCleanupUntil(SCOPE_LOOP, S->getSourceRange(), true);
  return true;
}

/// Visit the GotoStmt, emit the cleanup clauses for the levels until the
/// Label's scope.
bool CoroCRecursiveASTVisitor::VisitGotoStmt(GotoStmt *S) {
  emitCleanupWithLabel(S->getLabel(), S->getSourceRange());
  return true;
}

/// Visit the ReturnStmt, emit the cleanup clauses until the current fucntion
bool CoroCRecursiveASTVisitor::VisitReturnStmt(ReturnStmt *S) {
  Expr *RE = S->getRetValue();
  DeclRefExpr *DR = nullptr;
  
  if (RE != nullptr) {
    // If return the reference itself,
    // then ignore this refernce from the auto-cleanup list.
    if (IsCoroCAutoRefExpr(RE, &DR) && DR != nullptr) {
      bool isLocal = false;
      emitCleanupUntil(SCOPE_FUNC | SCOPE_FUNC_RET, S->getSourceRange(),
                       !isSingleReturnStmt, DR->getDecl(), &isLocal);
      if (!isLocal) {
        // NOTE: If the return ref is NOT A LOCAL ref,
        // maybe an argument passed by caller or a global ref,
        // then we should inc its refcnt value before return !!
        RewriteHelper RH(&Rewrite);
        RH << Indentation << "__refcnt_get(" << RE << ");" << Endl;
        RH.InsertText(S->getLocStart(), false);
      }
      return true;
    }
  
    // Try to find any reference in the return expression.
    CoroCAutoRefFinder Finder;
    Finder.TraverseStmt(RE);

    if (Finder.Found()) {
      // If found, just moving the return expression before
      // the auto-cleanup clauses, make a new temp var to hold
      // the value of the expression, and finally, return this
      // temp var instead of the orignal expression with ref inside.
      // Doing those just because we may release the references before
      // this ReturnStmt !!
      unsigned id = ++unique_id_generator;
      CoroCStmtPrinterHelper Helper(Rewrite.getLangOpts());
      RewriteHelper RH(&Rewrite, &Helper);

      emitCleanupUntil(RH, SCOPE_FUNC | SCOPE_FUNC_RET, 
                       S->getSourceRange(), false);
      
      if (!isSingleReturnStmt) 
        RH << "{ " << Endl << Indentation;

      RH << RE->getType().getCanonicalType() 
         << " __coroc_temp_ret_" << id
         << " = " << RE << ";" << Endl;

      RH.InsertText(S->getLocStart(), false);  

      RH << "__coroc_temp_ret_" << id;
      RH.ReplaceText(RE->getSourceRange());

      if (!isSingleReturnStmt) {
        RH << Endl << "}";
        RH.InsertTextAfterToken(getNextTokLocStart(S->getLocEnd()));
      }
    
      return false;
    }
  }

  emitCleanupUntil(SCOPE_FUNC | SCOPE_FUNC_RET, S->getSourceRange(), 
                  !isSingleReturnStmt);
  return true;
}

/// Rewrite the type name of __chan_t / __task_t, delete the attribute or add a
/// wrapper
void CoroCRecursiveASTVisitor::rewriteCoroCRefTypeName(NamedDecl *D, SourceLocation StartLoc,
                                                       QualType Ty, bool isTypedef) {                                                     
  Ty = Ty.getCanonicalType();
  if (!IsCoroCAutoRefType(Ty))
    return;
 
  // Check if the `__chan_t' or `__refcnt_t' with a type attribute
  SourceLocation EndLoc;
  Token TheTok = getNextTok(StartLoc);
  SourceLocation Loc = TheTok.getLocation();
  // FIXME : If more than one VarDecls share a type decl specifier,
  //         only the first one will update the type name correctly.
  //         This condition checks if the code has been rewritten yet, 
  //         note the method is ugly, but works.
  bool rewrite = false;
  bool isGenRef = IsCoroCGeneralRefType(Ty);

  if (TheTok.getKind() == tok::less) {
    rewrite = (Rewrite.getRewrittenText(Loc) == "<");
    unsigned n = 0;
    while (1) {
      if (TheTok.getKind() == tok::greater) n--;
      if (TheTok.getKind() == tok::less) n++;

      // delete the current Token
      if (rewrite && !isGenRef)
        Rewrite.ReplaceText(Loc, "");
      
      // TheTok must be a closed '>' when loop ends.
      if (n == 0) break;

      TheTok = getNextTok(Loc);
      Loc = TheTok.getLocation();
    } 
    // return the current end of code stream!! 
    EndLoc = Loc;
  
  } else {
    EndLoc = StartLoc;
  }

  // For `__refcnt_t<T>', we should update the typename
  if (rewrite && isGenRef) {
    QualType T = D->getRefElemType();
    std::string newName = ConvertTypeToSubName(T);
    newName = "struct __refcnt_" + newName + " *"; // To pointer type !!

    Rewrite.ReplaceText(SourceRange(StartLoc, EndLoc), newName);
    return;
  }

  // FIXME: if the current type source is from a TypedefDecl,
  //        we must translate the `__chan_t' into `tsc_chan_t' directly,
  //        since the `typedef X Y;' clause cannot be preprocessed in C!!
  if (!isTypedef) return;
  
  if (Ty == Context->ChanRefTy)
    Rewrite.ReplaceText(StartLoc, "tsc_chan_t");
  else if (Ty == Context->TaskRefTy)
    Rewrite.ReplaceText(StartLoc, "tsc_coroutine_t");
  else if (Ty == Context->GeneralRefTy)
    Rewrite.ReplaceText(StartLoc, "tsc_refcnt_t");
}

/// Fetch the base simple type from a given complex type.
/// e.g. 
///     if the Ty is `__chan_t []', return `__chan_t';
///     if the Ty is `__task_t *', return `__task_t'..
QualType CoroCRecursiveASTVisitor::getBaseRefType(QualType Ty) {
  Ty = Ty.getCanonicalType();
  bool loop;

  do {
    loop = false;
    if (Ty->isArrayType()) {
      Ty = Context->getBaseElementType(Ty);
      loop = true;
    }
    if (Ty->isPointerType()) {
      Ty = Ty->getPointeeType();
      loop = true;
    }
  } while (loop);

  return Ty;
}

void CoroCRecursiveASTVisitor::AddDefaultInit(ValueDecl *D, bool Simple) {
  VarDecl *VD = dyn_cast<VarDecl>(D);
  if (VD == nullptr || isa<ParmVarDecl>(D)) return;

  if (VD->hasInit()) {
    // FIXME: if it is a struct or array, how to handle it?
    if (!Simple) return ;

    Expr *Init = VD->getInit();
    if (!isa<CallExpr>(Init) && !isa<CoroCMakeChanExpr>(Init) &&
        !isa<CoroCSpawnCallExpr>(Init) && !isa<CoroCNewExpr>(Init) &&
        !IsNullToReference(Init, *Context)) {
      // need to add the refcnt of the init expr..
      Rewrite.InsertTextBefore(Init->getLocStart(), "__refcnt_get(");
      Rewrite.InsertTextAfterToken(Init->getLocEnd(), ")");
    }
  } else if (!D->hasExternalFormalLinkage()) {
    // FIXME: how to handle the N-Dimensional arrays or structs?
    if (Simple)
      Rewrite.InsertTextAfterToken(D->getLocEnd(), " = NULL");
    else
      Rewrite.InsertTextAfterToken(D->getLocEnd(), " = { 0 }");
  }
}

/// Override the ValueDecl when the type is CoroC Ref
bool CoroCRecursiveASTVisitor::VisitValueDecl(ValueDecl *D) {
  // Determine the type of the var
  QualType Ty = D->getType();  

  if (Ty.getTypePtrOrNull() == nullptr)
    return false; // ignore the undefined type value..
  
  if (Ty->isStructureType() && !isa<ParmVarDecl>(D)) {
    // FIXME: add the struct var to the scope anyway,
    // will check when emit the cleanup code later!!
    InsertRefToCurScope(D);
    AddDefaultInit(D, false);
    return true;
  }
  
  // fetch the simple type .
  QualType BaseTy = getBaseRefType(Ty);

  // If it is a `VarDecl', the typename will be rewrited when
  // visiting the `DeclStmt', because if we do it here, some errors
  // will happen when the there're more than 1 `VarDecl' in a `DeclStmt'.
  // FIXME: This will cause the global vars cannot be added into any scope!!
  SourceLocation StartLoc = D->getSourceRange().getBegin();
  rewriteCoroCRefTypeName(D, StartLoc, BaseTy);
  if (BaseTy == Context->GeneralRefTy) {
    QualType RefType = D->getRefElemType();
    if (RefType.getTypePtrOrNull() == nullptr)
      return false;
    AddRefcntType(RefType.getTypePtr());
#if 0
    std::string NewName = "struct __refcnt_" + ConvertTypeToSubName(RefType) + "*";
    Rewrite.ReplaceText(StartLoc, 10, NewName.c_str());
#endif
  }
  // NOTE: The `ParmVarDecl' will not be inserted into any scope!
  //       The caller will dec its counter when the function returns.
  if (isa<ParmVarDecl>(D)) return true;

  if (!Ty->isPointerType() && 
      IsCoroCAutoRefType(BaseTy)) {
    // Insert the reference to current scope
    InsertRefToCurScope(D);
    // If no init code, and a default to zero!
    AddDefaultInit(D, !Ty->isArrayType());
  }

  return true;
}

/// Find and fix the CallExpr which is not return back,
/// emit the cleanup code before it !!
bool CoroCRecursiveASTVisitor::VisitCallExpr(CallExpr *E) {
  FunctionDecl *FD = E->getDirectCallee();
  if (FD == nullptr) return true;
  
  // if this call will not return back, emit the cleanup code
  // for current fucntion scope.
  if (FD->isNoReturn() && 
      FD->getNameAsString() == "__CoroC_Exit")
    emitCleanupUntil(SCOPE_FUNC | SCOPE_FUNC_RET, 
                     E->getSourceRange(), !isSingleReturnStmt);
  return true;
}

/// If the MemberExpr 's base expr is a DeclRefExpr with '__refcnt_t<T>' 
/// type, convert the base expr into the C pointer inside.
bool CoroCRecursiveASTVisitor::VisitMemberExpr(MemberExpr *E) {
  Expr *BaseExpr = E->getBase();
  if (BaseExpr->getType().getCanonicalType() == Context->GeneralRefTy) {
    // __refcnt_t<T> ref = ...;
    // ref->... ==>
    //      ( &( (ref)->__obj[0] ) )->...
    RewriteHelper RH(&Rewrite);

    RH << "(&((";
    RH.InsertText(BaseExpr->getLocStart());

    RH << ")->__obj[0]))";
    RH.InsertTextAfterToken(BaseExpr->getLocEnd());
  }

  return true;
}

/// If the ArraySubscriptExpr 's base expr is a __refcnt_t type,
/// convert the base expr into the C pointer inside.
bool CoroCRecursiveASTVisitor::VisitArraySubscriptExpr(ArraySubscriptExpr* E) {
  Expr *BaseExpr = E->getBase();
  if (BaseExpr->getType().getCanonicalType() == Context->GeneralRefTy) {
    RewriteHelper RH(&Rewrite);

    RH << "(&((";
    RH.InsertText(BaseExpr->getLocStart());
    
    RH << ")->__obj[0]))";
    RH.InsertTextAfterToken(BaseExpr->getLocEnd());
  }
  return true;
}


/// Find and fix the binary operator expression.
/// By now, we just handle the CoroC channel operations and 
/// assignments for CoroC auto-references.
Expr *CoroCRecursiveASTVisitor::VisitBinaryOperator(BinaryOperator *B) {
  // Determine the type of this binary operator
  unsigned Opc = B->getOpcode();
  switch (Opc) {
  default:
    return B;
  case BO_Shl:
  case BO_Shr:
    return VisitChanOperator(B, Opc);
  case BO_Assign:
    return VisitAssignmentOperator(B);
  }
}

Expr *CoroCRecursiveASTVisitor::VisitDerefOperator(UnaryOperator *U, bool isAutoDeref) {
  // __refcnt_t <T> ptr = ...;
  // $(ptr)  ==> (&((ptr)->__obj[0]))
  // -- or --
  // *(ptr)  ==> ((ptr)->__obj[0])
  Expr *E = U->getSubExpr();
  if (E->getType().getCanonicalType() == Context->GeneralRefTy) {
    RewriteHelper RH(&Rewrite);

    if (isAutoDeref) {
      QualType ElemTy = U->getType();
      assert(ElemTy->isPointerType() && 
             "The `$' operator must return a pointer type!");
      RH << "(&";
    }
    
    RH << "((" << E << ")->__obj[0])";

    if (isAutoDeref) RH << ")";
    RH.ReplaceText(U->getSourceRange());
  }
  return U;
}

/// Find and fix the unary operator expression.
/// By now, wen just handle the CoroC refcnt addressing op.
Expr *CoroCRecursiveASTVisitor::VisitUnaryOperator(UnaryOperator *U) {
  unsigned Opc = U->getOpcode();
  switch (Opc) {
  default:
    return U;
  case UO_Deref:
  case UO_AutoDeref:
    return VisitDerefOperator(U, (Opc == UO_AutoDeref));
  }
}

/// Rewrite the assign operations for CoroC auto-reference type.
Expr *CoroCRecursiveASTVisitor::VisitAssignmentOperator(BinaryOperator *B) {
  Expr *LHS = B->getLHS();
  Expr *RHS = B->getRHS();

  if (!IsCoroCAutoRefType(LHS->getType()))
    return B;

  // replace the code "ref_a = ref_b;" to
  // "__refcnt_assign(ref_a, ref_b);"
  // which is a macro and can be expansioned as :
  if (IsCoroCAutoRefExpr(RHS))
    // "({__refcnt_put(ref_a); ref_a = __refcnt_get(ref_b); ref_a})"
    Rewrite.InsertTextBefore(LHS->getLocStart(), "__refcnt_assign(");
  else
    // "({__refcnt_put(ref_a); ref_a = ref_b; ref_a})"
    Rewrite.InsertTextBefore(LHS->getLocStart(), "__refcnt_assign_expr(");

  Rewrite.ReplaceText(B->getOperatorLoc(), B->getOpcodeStr().size(), ",");
  Rewrite.InsertTextAfterToken(RHS->getLocEnd(), ")");

  return B;
}

/// Override the BinaryOperator when it is a CoroC channel operation
Expr *CoroCRecursiveASTVisitor::VisitChanOperator(BinaryOperator *B,
                                                  unsigned Opc) {
  // Check if it's the channel operator..
  Expr *LHS = B->getLHS();
  Expr *RHS = B->getRHS();

  QualType LTy = LHS->getType().getCanonicalType();

  if (LTy == Context->ChanRefTy) {
    // Check if we can get the address of RHS directly
    bool usePtr;

    std::string FuncName;
    GetChanFuncname(RHS, Opc, FuncName, usePtr, Context, 
                    IsCoroCAutoRefType(RHS->getType()));

    // Insert the function call at the start of the first expr
    FuncName += "(";
    Rewrite.InsertText(LHS->getLocStart(), FuncName, true);

    // Replace the operator "<<" or ">>" with ","
    Rewrite.ReplaceText(B->getOperatorLoc(), B->getOpcodeStr().size(), ",");

    // The second param should be a pointer for runtime calls
    // FIXME: Check if the RHS is a L-Value for address operation!!
    if (usePtr) {
      Rewrite.InsertText(RHS->getExprLoc(), "&(");
      Rewrite.InsertTextAfterToken(RHS->getLocEnd(), "))");
    } else {
      Rewrite.InsertTextAfterToken(RHS->getLocEnd(), ")");
    }
  }

  return B;
}

/// Transform the __CoroC_New keyword
bool CoroCRecursiveASTVisitor::VisitCoroCNewExpr(CoroCNewExpr *E) {
  Expr *SizeExpr = E->getSizeExpr();
  Expr *FiniExpr = E->getFiniExpr();
  Expr *AppendExpr = E->getAppendExpr();

  QualType Ty = E->getElemType();
  // find the location of '<' and replace the text
  SourceLocation Loc = getNextTokLocStart(E->getLocStart());

  RewriteHelper RH(&Rewrite);
  
  if (Ty->isStructureType()) {
    // Transform to runtime call:
    //   __CoroC_New( __refcnt_Type_fini, __refcnt_Type, Type, 
    //                size, fini, append )
    RH << "(__refcnt_" << ConvertTypeToSubName(Ty) << "_fini, "
       << "struct __refcnt_" << ConvertTypeToSubName(Ty) << ", ";
    RH.ReplaceText(Loc);
   
    if (SizeExpr == nullptr) {
      RH << ", 1, NULL, 0)";
      RH.ReplaceText(E->getLocEnd());
    } else if (FiniExpr == nullptr) {
      RH << ", NULL, 0)";
      RH.ReplaceText(E->getLocEnd());
    } else if (AppendExpr == nullptr) {
      RH << ", 0)";
      RH.ReplaceText(E->getLocEnd());
    } else {
      Rewrite.ReplaceText(E->getLocEnd(), 1, ")");
    }
  } else {
    // for builtin and basic types, no specific destructors.
    //    __CoroC_New_Basic( __refcnt_Type, Type, size)
    
    RH << "__CoroC_New_Basic" 
       << "(struct __refcnt_" << ConvertTypeToSubName(Ty) 
       << ", " << Ty << ", ";

    if (SizeExpr == nullptr)
      RH << "1)";
    else
      RH << SizeExpr << ")";

    RH.ReplaceText(E->getSourceRange());
  }
  return true;
}

/// Transform the __CoroC_Spawn keyword
bool CoroCRecursiveASTVisitor::VisitCoroCSpawnCallExpr(CoroCSpawnCallExpr *E) {
  CallExpr *CE = E->getCallExpr();
  DeclRefExpr *G = E->getGroupRefExpr();
  int numArgs = CE->getNumArgs();
  bool noThunk = false;

  SourceLocation SpawnLoc = E->getLocStart();

  // If the spawn call has one pointer typed param,
  // we don't need to generate the thunk function wrapper.
  if (G == nullptr && numArgs == 1) {
    Expr *Arg = CE->getArg(0);
    noThunk = Arg->getType().getTypePtr()->isPointerType();
  }

  if (noThunk) {
    Expr *Callee = CE->getCallee();
    // Transform to runtime call:
    //  __CoroC_Spawn( (__CoroC_spawn_entry_t)func, param );
    Rewrite.InsertTextAfterToken(E->getLocStart(), "((__CoroC_spawn_entry_t)");

    SourceLocation Loc = getNextTokLocStart(Callee->getLocEnd());
    Rewrite.ReplaceText(Loc, 1, ", ");

  } else {
    // struct __thunk_struct_xxx Px = { ... };
    //  __CoroC_Spawn( __thunk_helper_xxx, Px );

    // generate a random unique temp name
    std::stringstream paramName;
    paramName << "__coroc_temp_" << unique_id_generator++;

    // get or create a new thunker
    ThunkHelper *Thunk = getOrCreateThunkHelper(CE, (G != nullptr));
    CoroCStmtPrinterHelper Helper(Rewrite.getLangOpts());
    RewriteHelper RH(&Rewrite, &Helper);

    RH << "{" << Endl;

    Thunk->DumpThunkCallPrologue(RH, CE, G, paramName.str());

    // insert the prologue before the __CoroC_Spawn keyword
    RH.InsertText(SpawnLoc);

    // replace all the CE's text ..
    std::string funcName, cleanupName("NULL");
    Thunk->GetFuncName(funcName);
    Thunk->GetCleanupName(cleanupName);

    // arg0 : entry function handler
    RH << "((__CoroC_spawn_entry_t)" << funcName << ", ";
    // arg1 : param pointer
    RH << paramName.str() << ", ";
    // arg2 : cleanup function handler
    RH << "(__CoroC_spawn_cleanup_t)" << cleanupName << ");";
    
    RH << Endl << "}";

    // delete the ';' in nextline
    SourceLocation Loc = getNextTokLocStart(CE->getLocEnd());
    Rewrite.ReplaceText(Loc, 1, "");

    // replace the text
    RH.ReplaceText(CE->getSourceRange());

    // remove the option section <...> after the '__CoroC_Spawn' keyword
    if (G != nullptr) {
      SourceLocation StartLoc = getNextTokLocStart(SpawnLoc); // the Loc of '<'
      SourceLocation EndLoc = getNextTokLocStart(G->getLocEnd()); // the Loc of '>'
      
      Rewrite.RemoveText(SourceRange(StartLoc, EndLoc));
      // stop to traverse the GroupRefExpr 
      E->setGroupRefExpr(nullptr);
    }

    // replace the '__CoroC_Spawn' with '__CoroC_Spawn_Opt'
    Rewrite.InsertTextAfterToken(SpawnLoc, "_Opt");

    // stop to traverse the CallExpr since it has been replaced
    E->setCallExpr(nullptr);
  }

  return true;
}

/// Transform the __CoroC_Async_Call keyword
bool CoroCRecursiveASTVisitor::VisitCoroCAsyncCallExpr(CoroCAsyncCallExpr *E) {
  CallExpr *CE = E->getCallExpr();
  int numArgs = CE->getNumArgs();

  SourceLocation AsyncLoc = E->getLocStart();
  Expr *Callee = CE->getCallee();
  QualType Ty = E->getType();
  bool isVoidTy = (Ty == Context->VoidTy);
  
  if (numArgs == 0 && isVoidTy) {
    // no need generate the thunk wrraper.
    // Transform "__CoroC_Async_Call func()"
    //   to "__CoroC_Async_Call( (__CoroC_async_hanlder_t)func, NULL)"
    Rewrite.InsertTextAfterToken(AsyncLoc, "( (__CoroC_async_handler_t)");
    SourceLocation Loc = getNextTokLocStart(Callee->getLocEnd()); // the '(' after func
    Rewrite.ReplaceText(Loc, 1, ", ");
  }
  else {
    // generate a random unique temp name
    std::stringstream paramName;
    paramName << "__coroc_temp_" << unique_id_generator++;

    // get or create a new thunker
    ThunkHelper *Thunk = getOrCreateThunkHelper(CE, /*isGroupOp=*/false, /*isAsync=*/true);
    CoroCStmtPrinterHelper Helper(Rewrite.getLangOpts());
    RewriteHelper RH(&Rewrite, &Helper);

    if (!isVoidTy) RH << "("; // !!
    RH << "{" << Endl; 

    Thunk->DumpThunkCallPrologue(RH, CE, nullptr, paramName.str());

    RH.InsertText(AsyncLoc);

    // replace all the CE's text ..
    std::string funcName;
    Thunk->GetFuncName(funcName);

    // arg0 : async function handler
    RH << "((__CoroC_async_handler_t)" << funcName << ", ";
    // arg1 : param pointer
    RH << paramName.str() << ");" << Endl;
    
    // record the return value and release the param ..
    if (!isVoidTy) {
      RH << Indentation << Ty << " __ret = " 
         << paramName.str() << "->_ret;" << Endl 
         << Indentation << "free(" << paramName.str() << ");" << Endl 
         << Indentation << "__ret; });" << Endl;
    } else {
      RH << Indentation << "free(" << paramName.str() <<");" << Endl 
         << "}" << Endl;
    }

    // repalce the orignal callexpr's text ..
    RH.ReplaceText(CE->getSourceRange());

    // delete the ';' in nextline
    SourceLocation Loc = getNextTokLocStart(CE->getLocEnd());
    Rewrite.ReplaceText(Loc, 1, "");
  }

  return true;
}

/// Transform the __CoroC_Chan keyword
bool CoroCRecursiveASTVisitor::VisitCoroCMakeChanExpr(CoroCMakeChanExpr *E) {
  Expr *CE = E->getCapExpr();
  SourceLocation ChanLoc = E->getLocStart();
  QualType BaseTy = getBaseRefType(E->getElemType());

  // Transform to runtime call:
  //  __CoroC_Chan(sizeof type, (expr), isref);
  CoroCStmtPrinterHelper Helper(Rewrite.getLangOpts());
  RewriteHelper RH(&Rewrite, &Helper);
  
  RH << "__CoroC_Chan(" << "sizeof(" << BaseTy << "), ";
  
  if (CE == nullptr) RH << "0, ";
  else RH << CE << ", ";

  RH << (IsCoroCAutoRefType(BaseTy) ? "1" : "0") << ")";

  RH.ReplaceText(SourceRange(ChanLoc, E->getGTLoc()));

  return false;
}

/// Transform the __CoroC_Quit keyword
bool CoroCRecursiveASTVisitor::VisitCoroCQuitStmt(CoroCQuitStmt *S) {
  Expr *RE = S->getReturnExpr();
  SourceLocation QuitLoc = S->getLocEnd();
  if (RE == nullptr) {
    Rewrite.InsertTextAfterToken(QuitLoc, "(0)");
    emitCleanupUntil(SCOPE_FUNC, SourceRange(S->getLocStart()), !isSingleReturnStmt);
  } else {
    Rewrite.InsertTextAfterToken(QuitLoc, "(");
    Rewrite.InsertTextAfterToken(RE->getLocEnd(), ")");
    SourceRange SR(S->getLocStart(), RE->getLocEnd());
    emitCleanupUntil(SCOPE_FUNC, SR, !isSingleReturnStmt);
  }

  return true;
}

/// Transform the __CoroC_Yield keyword
bool CoroCRecursiveASTVisitor::VisitCoroCYieldStmt(CoroCYieldStmt *S) {
  Rewrite.InsertTextAfterToken(S->getLocEnd(), "()");
  return true;
}

/// Transform the __CoroC_Select keyword
bool CoroCRecursiveASTVisitor::VisitCoroCSelectStmt(CoroCSelectStmt *S) {
  CompoundStmt *CS = reinterpret_cast<CompoundStmt *>(S->getBody());
  bool hasDef = false;
  CompoundStmt::body_iterator itr = CS->body_begin();
  for (; itr != CS->body_end() && !hasDef; ++itr) {
    CoroCCaseStmt *Case = reinterpret_cast<CoroCCaseStmt *>(*itr);
    if (Case->getChanOpExpr() == nullptr)
      hasDef = true;
  }

  SelectHelper *SH =
      new SelectHelper(Context, Rewrite, 
                       unique_id_generator++, 
                       CS->getLocStart(),
                       CS->getLocEnd(), 
                       CS->size(), hasDef);
  SH->GenPrologueAndEpilogue();
  pushSelStk(SH);

  // Remove the keyword `__CoroC_Select'.
  Rewrite.RemoveText(SourceRange(S->getSelectLoc()));
  return true;
}

/// Transform the __CoroC_Case / __CoroC_Default
bool CoroCRecursiveASTVisitor::VisitCoroCCaseStmt(CoroCCaseStmt *S) {
  SelectHelper *SH = popSelStk();
  assert(SH != nullptr);

  if (SH->RewriteCaseStmt(S)) {
    pushSelStk(SH);
  } else {
    SH->DumpPrologueAndEpilogue();
    delete SH;
  }

  // FIXME : better way to stop traverse the ChanOpExpr
  S->setChanOpExpr(nullptr);
  return true;
}

RewriteCoroC::RewriteCoroC(const std::string &inFile, raw_ostream *OS,
                           DiagnosticsEngine &D, const LangOptions &LOpt)
    : Diags(D), LangOpts(LOpt), InFileName(inFile), OutFile(OS),
      Visitor(nullptr) {
  // TODO
}

RewriteCoroC::~RewriteCoroC() {
  if (Global != nullptr) delete Global;
  if (Visitor != nullptr) delete Visitor;
}

void RewriteCoroC::Initialize(ASTContext &C) {
  Context = &C;
  SM = &C.getSourceManager();
  Rewrite.setSourceMgr(C.getSourceManager(), C.getLangOpts());
  Visitor = new CoroCRecursiveASTVisitor(Rewrite, Context);
  Global = new ScopeHelper(Visitor, SourceRange(), SCOPE_GLOBAL); // FIXME!!
}

bool RewriteCoroC::HandleTopLevelDecl(DeclGroupRef D) {
  typedef DeclGroupRef::iterator iter;
  RewriteHelper RH(&Rewrite);

  bool printDecl = false;

  for (iter I = D.begin(); I != D.end(); ++I) {
    Visitor->TraverseDecl(*I);
    // Dump the thunk helpers if any exist
    Visitor->DumpThunkHelpers(RH);
    
    SourceLocation Loc = (*I)->getLocStart();

    if (printDecl && isa<TypedefDecl>(*I)) {
      printDecl = false; 
    } else {
      printDecl = false;
      // Dump the wrapper types for auto refcnt
      // NOTE: If the current the Decl is a struct/union defination
      //       we'll delay dumping the accroding refcnt wrapper type
      //       to avoid the case which the refcnt wrapper type need 
      //       the current struct/union 's defination!!
      if (isa<RecordDecl>(*I)) {
        Visitor->DeclareRefcntTypes(RH);
      
        // FIXME: If the code is like : 
        //            typedef struct {...} XXXX;
        //        then we should move the refcnt type declarations
        //        before the keyword `typedef' !!
        if ((I + 1) != D.end() && isa<TypedefDecl>(*(I + 1))) {
          TypedefDecl *TD = dyn_cast<TypedefDecl>(*(I + 1));
          TypeLoc TyLoc = TD->getTypeSourceInfo()->getTypeLoc();
          if (TyLoc.getBeginLoc() == Loc) {
            Loc = TD->getLocStart();
            printDecl = true;
          }
        }
      } else {
        Visitor->DumpRefcntTypes(RH);
      }
    }

    RH.InsertText(Loc);
  }

  return true;
}

void RewriteCoroC::HandleTranslationUnit(ASTContext &C) {
  // print the new file buffer ..
  (*OutFile)
      << "/* C source file auto generated by Clang CoroC rewriter. */\n";
  (*OutFile) << "#include <libcoroc.h>\n";

  const RewriteBuffer *RewriteBuf =
      Rewrite.getRewriteBufferFor(SM->getMainFileID());

  // check if the input file is empty.
  if (RewriteBuf == nullptr || RewriteBuf->size() == 0) return;

  (*OutFile) << std::string(RewriteBuf->begin(), RewriteBuf->end());

  // dump the remained refcnt types ..
  RewriteHelper RH(&Rewrite);
  Visitor->DumpRefcntTypes(RH);
  RH.Dump(*OutFile);

  // generate the wrapper call to __CoroC_UserMain
  if (Visitor->HasMain()) {
    (*OutFile) << "\n/* wrapper call to __CoroC_UserMain */\n";
    (*OutFile) << "int user_main(int argc, char **argv) {\n\t";
    (*OutFile) << "__CoroC_UserMain(argc, argv);\n\t";
    (*OutFile) << "return 0;\n}\n";
    (*OutFile) << "/* end of the wrapper call */\n";
  }
}

ASTConsumer *clang::CreateCoroCRewriter(const std::string &InFile,
                                        raw_ostream *OS,
                                        DiagnosticsEngine &Diags,
                                        const LangOptions &LOpts) {
  return new RewriteCoroC(InFile, OS, Diags, LOpts);
}
