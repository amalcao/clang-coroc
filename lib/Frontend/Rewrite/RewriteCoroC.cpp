//===--- RewriteCoroC.cpp - Playground for the code rewriter ---------------===//
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
  /// \brief Get the expansion location of a keyword
  static SourceLocation GetExpansionLoc(Rewriter& Rewrite, SourceLocation Loc) {
    return Rewrite.getSourceMgr().getExpansionLoc(Loc);
  }

  /// \brief Get the runtime function name of the given channel operand
  static void GetChanFuncname(ASTContext& Ctx, Expr *RHS, unsigned Opc, 
                       std::string &funcName, bool &usePtr, 
                       bool sel = false, bool nonBlock = false) {
    
    bool isNil = (dyn_cast<CoroCNullExpr>(RHS) != nullptr);
    funcName = sel ? "__CoroC_Select_" : "__CoroC_Chan_";

    // FIXME : use a better way to get if the address of the RHS expr
    // can be caluculated by the '&' operator.
    usePtr = !isNil && 
             (RHS->isModifiableLvalue(Ctx, nullptr) == Expr::MLV_Valid);

    if (Opc == BO_Shr) 
      funcName += "Recv";
    else {
      funcName += "Send";
      if (!usePtr)
        funcName += "Expr";
    }

    if (nonBlock) funcName += "_NB";

    return;
  }

  /// \brief Thunk helper function for Spawn Operator
  class ThunkHelper {
    ASTContext *Context;
    Rewriter &Rewrite;

    CallExpr *TheCallExpr;
    std::string ThunkUID;
    bool hasDump;
  
    void dumpThunkStruct(std::ostream& OS);
    void dumpThunkFuncArgsType(std::ostream& OS, 
                               const FunctionProtoType* FuncTy);
    void dumpThunkFunc(std::ostream& OS);

  public:
    ThunkHelper(ASTContext *C, Rewriter &R, 
                CallExpr *CE, std::string UID) 
      : Context(C), Rewrite(R)
      , TheCallExpr(CE), ThunkUID(UID), hasDump(false) { }
    
    bool MatchCallExpr(CallExpr *CE);

    void DumpThunkCallPrologue(std::ostream& OS,
                               CallExpr* CE, 
                               std::string paramName);
    
    void GetFuncName(std::string& funcName);
    void GetStructName(std::string& structName);

    bool HasDump() { return hasDump; }

    void Dump(std::ostream& OS) {
      if (!hasDump) {
        OS << "\n/// auto generated by CoroC rewriter.\n";
        dumpThunkStruct(OS);
        dumpThunkFunc(OS);
        OS << "\n/// end\n\n";
        hasDump = true;
      }
    }
  };

  /// \brief Select Helper for generating the code for '__CoroC_Select'
  class SelectHelper {
    ASTContext *Context;
	Rewriter &Rewrite;
	std::string SelUID;
	SourceLocation StartLoc, EndLoc;

	unsigned CaseNum;
	unsigned CurPos;

    bool HasDefault;
    bool SimpleWay;

	std::stringstream Prologue, Epilogue;

  public:
    SelectHelper(ASTContext *Ctx, Rewriter &R, std::string UID,
				 SourceLocation SL, SourceLocation EL,
				 unsigned Num, bool hasDef)
	  : Context(Ctx), Rewrite(R), SelUID(UID), StartLoc(SL), EndLoc(EL)
	  , CaseNum(Num), CurPos(0), HasDefault(hasDef), SimpleWay(false) {
        if (CaseNum == 1 || 
		    (CaseNum == 2 && HasDefault))
          SimpleWay = true;
      }
	
	void DumpPrologueAndEpilogue() {
      if (!SimpleWay) {
	    Prologue << "\t\t__chan_t __select_result_"
			     << SelUID << " = __CoroC_Select(__select_set_"
			     << SelUID << ", " << !HasDefault << ");\n";
      }

	  Rewrite.InsertTextAfterToken(StartLoc, Prologue.str());
	  Rewrite.InsertTextBefore(EndLoc, Epilogue.str());
	}

	void GenPrologueAndEpilogue() {
      if (SimpleWay) return;

	  int num = HasDefault ? CaseNum - 1 : CaseNum;
	  Prologue << "\n\t\t__select_set_t __select_set_" << SelUID
	  		   << " = __CoroC_Select_Alloc(" << num << ");\n"; 

	  Epilogue << "\n\t\t__CoroC_Select_Dealloc(__select_set_"
	  		   << SelUID << ");\n\t";
	}
	
	void InsertCaseInitialization(BinaryOperator *BO) {
      std::string FuncName;
      bool UsePtr;
      GetChanFuncname(*Context, BO->getRHS(), BO->getOpcode(),
                      FuncName, UsePtr, !SimpleWay, SimpleWay);

      if (SimpleWay)
        Prologue << "\n\t\tbool __select_result_" << SelUID
                 << " = " << FuncName << "(";
      else
	    Prologue << "\t\t" << FuncName << "(__select_set_"
	  			 << SelUID << ", ";
	  
      Prologue << "*(" << Rewrite.ConvertToString(BO->getLHS()) << "), ";
	  
	  if (UsePtr)
	    Prologue << "&(" << Rewrite.ConvertToString(BO->getRHS()) <<")";
	  else
	    Prologue << Rewrite.ConvertToString(BO->getRHS());

	  Prologue << ");\n";
	}

	bool RewriteCaseStmt(CoroCCaseStmt *Case) {
	  std::stringstream SS;

	  if (CurPos == 0)
    	SS << "if (";
	  else
		SS << "else if (";

      SourceLocation SL = 
        GetExpansionLoc(Rewrite, Case->getLocStart());
      SourceRange SR(SL);

	  Expr *E = Case->getChanOpExpr();
	  if (E != nullptr) {
	    ParenExpr *PE = dyn_cast<ParenExpr>(E);
		assert(PE != nullptr);
        SR.setEnd(PE->getLocEnd());

		BinaryOperator *BO = reinterpret_cast<BinaryOperator*>(PE->getSubExpr());
		InsertCaseInitialization(BO);

        if (!SimpleWay)
	      SS << "*(" << Rewrite.ConvertToString(BO->getLHS()) << ") == ";
		     
        SS << "__select_result_" << SelUID << ")";

      } else {
	    SS << "!__select_result_" << SelUID << ")";
	  }

	  Rewrite.ReplaceText(SR, SS.str());

	  return (++CurPos < CaseNum); 
	}

  };

  /// \brief Recursive visit everything in AST, and make the translation.
  class CoroCRecursiveASTVisitor 
      : public RecursiveASTVisitor<CoroCRecursiveASTVisitor> 
  {
    static long unique_id_generator;

    Rewriter &Rewrite;
    ASTContext *Context;
    bool hasMain;

    std::vector<ThunkHelper*> ThunkPool; 
	std::vector<SelectHelper*> SelStk;

    Token getNextTok(SourceLocation CurLoc);
    SourceLocation getNextTokLocStart(SourceLocation CurLoc);
    ThunkHelper *getOrCreateThunkHelper(CallExpr *C);
	bool rewriteCoroCRefTy(Expr *E);
	void rewriteCoroCRefTypeName(SourceLocation, QualType, bool);
	void pushSelStk(SelectHelper *Helper);
	SelectHelper* popSelStk();


  public:
    CoroCRecursiveASTVisitor(Rewriter &R, ASTContext *C) 
      : Rewrite(R), Context(C), hasMain(false) { }

    ~CoroCRecursiveASTVisitor();
 
    void DumpThunkHelpers(std::ostream&);
     
	bool VisitValueDecl(ValueDecl *D);
    bool VisitFunctionDecl(FunctionDecl *D);

    bool VisitCoroCSpawnCallExpr(CoroCSpawnCallExpr *E);
    bool VisitCoroCMakeChanExpr(CoroCMakeChanExpr *E);
    bool VisitCoroCYieldStmt(CoroCYieldStmt *S);
    bool VisitCoroCQuitStmt(CoroCQuitStmt *S);

	bool VisitCoroCCaseStmt(CoroCCaseStmt *S);
	bool VisitCoroCSelectStmt(CoroCSelectStmt *S);

	bool VisitArraySubscriptExpr(ArraySubscriptExpr *E);
    bool VisitDeclRefExpr(DeclRefExpr *E);
    bool VisitMemberExpr(MemberExpr *E);

	Expr *VisitBinaryOperator(BinaryOperator *B);

    bool HasMain() { return hasMain; }
  };

  /// \brief 
  class RewriteCoroC : public ASTConsumer {
    DiagnosticsEngine &Diags;
    const LangOptions &LangOpts;
    ASTContext *Context;
    SourceManager *SM;
    std::string InFileName;
    raw_ostream* OutFile;
    CoroCRecursiveASTVisitor *Visitor;

    Rewriter Rewrite;
    
  public:

    void Initialize(ASTContext &context) override;

    // Top Level Driver code.
    bool HandleTopLevelDecl(DeclGroupRef D) override; 
    void HandleTopLevelSingleDecl(Decl *D);
    void HandleDeclInMainFile(Decl *D);
    RewriteCoroC(const std::string &inFile, raw_ostream *OS,
                DiagnosticsEngine &D, const LangOptions &LOpts);

    ~RewriteCoroC() { 
      if (Visitor != nullptr) 
        delete Visitor; 
    }

    void HandleTranslationUnit(ASTContext &C) override;

  };
}

using namespace ict;

/// Match if the current thunk is suitable for the given CallExpr
bool ThunkHelper::MatchCallExpr(CallExpr *CE) {
  if (!TheCallExpr || !CE) return false;
  // compare the two names, that methord works for C env
  return Rewrite.ConvertToString(TheCallExpr->getCallee()) ==
            Rewrite.ConvertToString(CE->getCallee());
}

/// Get the name of the thunk helper function
void ThunkHelper::GetFuncName(std::string &funcName) {
  funcName = "__thunk_helper_";
  funcName += ThunkUID;
}

/// Get the typename of the thunk helper's param 
void ThunkHelper::GetStructName(std::string &structName) {
  structName = "__thunk_struct_";
  structName += ThunkUID;
}

/// Dump the thunk calling code into the OS
void ThunkHelper::DumpThunkCallPrologue(std::ostream &OS, 
                                        CallExpr *CE,
                                        std::string paramName) {
  // If the func call without any arg, ignore it!
  // if (CE->getNumArgs() == 0) return;
  
  OS << "\n\tstruct __thunk_struct_" << ThunkUID 
     << "*  " << paramName << " = (" 
     << "struct __thunk_struct_" << ThunkUID
     << "*)::malloc(sizeof("
     << "struct __thunk_struct_" << ThunkUID << "));\n\t";
  
  // Init each arg
  int i = 0;
  CallExpr::arg_iterator it = CE->arg_begin();
  for (; it != CE->arg_end(); ++it) {
    OS << paramName << "->_param" << i++ << " = ";
    
    Expr *E = *it;
    QualType Ty = E->getType();

    if (Ty == Context->ChanRefTy ||
        Ty == Context->TaskRefTy) {
      OS << "__refcnt_get(*" 
         << Rewrite.ConvertToString(E) << ")";
    } else
      OS << Rewrite.ConvertToString(E);

    OS << ";\n\t";
  }

  // Init the function pointer
  OS << paramName << "->_fp = (void*)(" 
     << Rewrite.ConvertToString(CE->getCallee()) << ");\n\t";
}

/// Dump the thunk param struct's body
void ThunkHelper::dumpThunkStruct(std::ostream &OS) {
  //if (TheCallExpr->getNumArgs() == 0) return;

  OS << "\nstruct __thunk_struct_" 
     << ThunkUID << " { \n";

  int i = 0;
  CallExpr::arg_iterator it = TheCallExpr->arg_begin();
  for (; it != TheCallExpr->arg_end(); ++it) {
    OS << "\t" << (*it)->getType().getAsString()
       << " _param" << i++ << ";\n";
  }
  OS << "\tvoid *_fp;\n};\n"; 
}

/// Dump the thunk function's arglist types
void ThunkHelper::dumpThunkFuncArgsType(std::ostream &OS, 
                                    const FunctionProtoType *FuncTy) {

   unsigned numArgs = FuncTy->getNumParams();
   for (unsigned i = 0; i < numArgs; ++i) {
    QualType Ty = FuncTy->getParamType(i);
    if (Ty == Context->ChanRefTy || Ty == Context->TaskRefTy)
      OS << "__CXX_refcnt_t<" << Ty.getAsString() << " >";
    else
      OS << Ty.getAsString();
    
    if (i < numArgs - 1)
      OS << ", ";
  }
}

/// Dump the thunk function defination
void ThunkHelper::dumpThunkFunc(std::ostream &OS) {
  unsigned numArgs = TheCallExpr->getNumArgs();
  Expr *E = TheCallExpr->getCallee();

  // Generate the func declaration:
  OS << "\nstatic int __thunk_helper_"
     << ThunkUID << "(";
/**
  if (numArgs == 0)
    OS << "void*";
  else*/
    OS << "struct __thunk_struct_" << ThunkUID << " *";
  
  OS << "_arg) {\n\t";
  
  // Generate the func body:

  // 1. decalarate a pointer to the callee
  QualType T = E->getType();
  assert(T->isPointerType());

  const Type *Ty = T->getPointeeType()->getUnqualifiedDesugaredType();
  assert(isa<FunctionProtoType>(Ty));

  const FunctionProtoType *FuncTy = 
            reinterpret_cast<const FunctionProtoType*>(Ty);

  OS << TheCallExpr->getType().getAsString() << " (*fp) (";
  
  dumpThunkFuncArgsType(OS, FuncTy);

  OS << ");\n\t";

  // 2. assign the callee address to the `fp'
  OS << "fp = (typeof(fp))(_arg->_fp);\n\t";

  // 3. calling the thunk helper function
  OS << "fp(";

  std::vector<int> ArgStk;
  if (numArgs > 0) {
    int i = 0;
    CallExpr::arg_iterator it = TheCallExpr->arg_begin();
    for (;;) {
      QualType Ty = (*it)->getType();
      if (Ty == Context->ChanRefTy || Ty == Context->TaskRefTy)
        ArgStk.push_back(i);

      OS << "_arg->_param" << i++;
      if (++it == TheCallExpr->arg_end()) break;
      OS << ", ";
    }
  }

  OS << ");\n\t";
  
  // 3. release the auto-references if any exisit
  for (unsigned k = 0; k < ArgStk.size(); ++k) {
    OS << "__refcnt_put(_arg->_param" << ArgStk[k] << ");\n\t";
  }

  // 4. release the _arg and quit
  if (numArgs > 0)
    OS << "::free(_arg);\n\t";
  OS << "__CoroC_Quit(0);\n}\n";
}

/// The static item of the CoroCRecursiveASTVisitor 
long CoroCRecursiveASTVisitor::unique_id_generator = 0;

/// The destructor of the CoroCRecursiveASTVisitor
CoroCRecursiveASTVisitor::~CoroCRecursiveASTVisitor() {
  std::vector<ThunkHelper*>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it) 
    delete (*it);
}

/// Get and return the next token after the one in current location
Token CoroCRecursiveASTVisitor::getNextTok(SourceLocation CurLoc) {
  int offset = Lexer::MeasureTokenLength(CurLoc, 
                                         Rewrite.getSourceMgr(),
                                         Rewrite.getLangOpts());
  
  Token TheTok;
  assert (!Lexer::getRawToken(CurLoc.getLocWithOffset(offset), 
                              TheTok,
                              Rewrite.getSourceMgr(),
                              Rewrite.getLangOpts(),
                              true));
  return TheTok;  
}

/// Get the next token after the one in current location
/// and return the source location of that token.
SourceLocation CoroCRecursiveASTVisitor::getNextTokLocStart(SourceLocation CurLoc) {
  Token TheTok = getNextTok(CurLoc);
  return TheTok.getLocation();
}

/// Dump all thunk helpers' code if neccessary..
void CoroCRecursiveASTVisitor::DumpThunkHelpers(std::ostream &OS) {
  std::vector<ThunkHelper*>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it)
    (*it)->Dump(OS);
}

/// Get or Create a thunk helper for CoroC Spawn Call
ThunkHelper* CoroCRecursiveASTVisitor::getOrCreateThunkHelper(CallExpr *C) {
  std::vector<ThunkHelper*>::iterator it = ThunkPool.begin();
  for (; it != ThunkPool.end(); ++it) {
    if ((*it)->MatchCallExpr(C))
      return (*it);
  }

  std::stringstream SS;
  SS << unique_id_generator++;

  ThunkHelper *Thunk = 
    new ThunkHelper(Context, Rewrite, C, SS.str());

  ThunkPool.push_back(Thunk);
  return Thunk;
}

/// Push / Pop the SelectHelper Stack
void CoroCRecursiveASTVisitor::pushSelStk(SelectHelper *Helper) {
  SelStk.push_back(Helper);
}

SelectHelper* CoroCRecursiveASTVisitor::popSelStk() {
  if (SelStk.empty())
  	return nullptr;
  SelectHelper *SH = SelStk.back();
  SelStk.pop_back();
  return SH;
}

/// Visit the FunctionDecl, change the `main' to `__CoroC_UserMain'
bool CoroCRecursiveASTVisitor::VisitFunctionDecl(FunctionDecl *D) {
  if (D->getDeclName()) {
    if (D->getNameAsString() == "main") {
      SourceLocation SL = D->getNameInfo().getLoc();
      Rewrite.ReplaceText(SL, 4, "__CoroC_UserMain");
      hasMain = true;
    }
  }
  
  bool isPointer = false;
  QualType Ty = D->getReturnType();
  if (Ty->isPointerType()) {
    isPointer = true;
	Ty = Ty.getTypePtr()->getPointeeType();
  }

  SourceLocation StartLoc = D->getReturnTypeSourceRange().getBegin();
  rewriteCoroCRefTypeName(StartLoc, Ty, !isPointer);

  return true;
}

/// Rewrite the type name of __chan_t / __task_t, delete the attribute or add a wrapper
void CoroCRecursiveASTVisitor::rewriteCoroCRefTypeName(SourceLocation StartLoc, QualType Ty, bool addWrapper) {
  Ty = Ty.getCanonicalType();
  if (Ty != Context->ChanRefTy && Ty != Context->TaskRefTy) 
    return;

  // Check if the `__chan_t' with a type attribute
  Token TheTok = getNextTok(StartLoc);
  if (TheTok.getKind() == tok::less) {
    while (TheTok.getKind() != tok::greater) {
      SourceLocation Loc = TheTok.getLocation();
      TheTok = getNextTok(Loc);
      Rewrite.ReplaceText(Loc, "");
    }
    Rewrite.ReplaceText(TheTok.getLocation(), ""); // delete the '>'
  }
  if (addWrapper) {
    StartLoc = GetExpansionLoc(Rewrite, StartLoc);
    if (Ty == Context->ChanRefTy) 
      Rewrite.ReplaceText(StartLoc, "__CXX_refcnt_t<__chan_t >");
    else
      Rewrite.ReplaceText(StartLoc, "__CXX_refcnt_t<__task_t >");
  }
}

/// Override the ValueDecl when the type is CoroC Ref
bool CoroCRecursiveASTVisitor::VisitValueDecl(ValueDecl *D) {
  // Determine the type of the var
  bool isPointer = false;
  QualType Ty = D->getType();
  if (Ty->isArrayType())
    Ty = Context->getBaseElementType(Ty);
  else if (Ty->isPointerType()) {
  	Ty = Ty.getTypePtr()->getPointeeType();
	isPointer = true;
  }

  SourceLocation StartLoc = D->getSourceRange().getBegin();
  rewriteCoroCRefTypeName(StartLoc, Ty, !isPointer);
  
  return true;
}


/// Find and fix the ChanRef & TaskRef if they are as the array elements
bool CoroCRecursiveASTVisitor::rewriteCoroCRefTy(Expr *E) {
  // Determine the type of the ref
  QualType Ty = E->getType();
  if (Ty == Context->TaskRefTy || Ty == Context->ChanRefTy)  {
    if (!E->isLValue()) {
      Rewrite.InsertText(E->getLocStart(), "*(");
	  Rewrite.InsertTextAfterToken(E->getLocEnd(), ")");
	}
  }
  return true;
}

/// Find and fix the ChanRef & TaskRef if they are as the array elements
bool CoroCRecursiveASTVisitor::VisitArraySubscriptExpr(ArraySubscriptExpr *E) {
  return rewriteCoroCRefTy(E);
}

/// Find and fix the ChanRef & TaskRef if they are as the struct / union members
bool CoroCRecursiveASTVisitor::VisitMemberExpr(MemberExpr *E) {
  return rewriteCoroCRefTy(E);
}

/// Find and fix the ChanRef & TaskRef
bool CoroCRecursiveASTVisitor::VisitDeclRefExpr(DeclRefExpr *E) {
  return rewriteCoroCRefTy(E);
}

/// Override the BinaryOperator when it is a CoroC channel operation
Expr *CoroCRecursiveASTVisitor::VisitBinaryOperator(BinaryOperator *B) {
  // Determine the type of this binary operator
  unsigned Opc = B->getOpcode();

  if (Opc != BO_Shl && Opc != BO_Shr) 
    return B;
  
  // Check if it's the channel operator..
  Expr *LHS = B->getLHS();
  Expr *RHS = B->getRHS();

  if (LHS->getType() == Context->ChanRefTy) {
    // Check if we can get the address of RHS directly
    bool UsePtr;
    std::string FuncName;
    GetChanFuncname(*Context, RHS, Opc, FuncName, UsePtr);

    // Insert the function call at the start of the first expr
    FuncName += "(";
    Rewrite.InsertText(LHS->getLocStart(), FuncName, true);

    // Replace the operator "<<" or ">>" with ","
    Rewrite.ReplaceText(B->getOperatorLoc(),
                      B->getOpcodeStr().size(), ",");
  
    // The second param should be a pointer for runtime calls
    // FIXME: Check if the RHS is a L-Value for address operation!!
    if (!UsePtr) {
      Rewrite.InsertTextAfterToken(RHS->getLocEnd(), ")");
    } else {
      Rewrite.InsertText(RHS->getExprLoc(), "&(");
      Rewrite.InsertTextAfterToken(RHS->getLocEnd(), "))");
    }
  }

  return B;
}

/// Transform the __CoroC_Spawn keyword
bool CoroCRecursiveASTVisitor::VisitCoroCSpawnCallExpr(CoroCSpawnCallExpr *E) {
  CallExpr *CE = E->getCallExpr();
  int numArgs = CE->getNumArgs();
  bool noThunk = false;
  
  SourceLocation SpawnLoc = GetExpansionLoc(Rewrite, E->getLocStart());
  if (numArgs == 1) {
    Expr *Arg = CE->getArg(0);
    noThunk = Arg->getType().getTypePtr()->isPointerType();
  }
    
  if (noThunk) {
    Expr *Callee = CE->getCallee();
    // Transform to runtime call:
    //  __CoroC_Spawn( (__CoroC_spawn_handler_t)func, param );
    Rewrite.InsertTextAfterToken(E->getLocEnd(), 
                               "((__CoroC_spawn_handler_t)");

    SourceLocation Loc = getNextTokLocStart(Callee->getLocEnd());
    Rewrite.ReplaceText(Loc, 1, ", ");
  
  } else {
    // struct __thunk_struct_xxx Px = { ... };
    //  __CoroC_Spawn( __thunk_helper_xxx, Px );
    
    // generate a random unique temp name
    std::stringstream paramName;
    paramName << "__coroc_temp_" << unique_id_generator++;

    // get or create a new thunker
    ThunkHelper *Thunk = getOrCreateThunkHelper(CE);
    std::stringstream SS;

    if (numArgs != 0) SS << "\n\t{";

    Thunk->DumpThunkCallPrologue(SS, CE, paramName.str());
    
    // insert the prologue before the __CoroC_Spawn keyword
    Rewrite.InsertText(SpawnLoc, SS.str());
    
    // replace all the CE's text ..
    std::string funcName;
    Thunk->GetFuncName(funcName);
    std::stringstream SS1;
    SS1 << "((__CoroC_spawn_handler_t)" << funcName << ", ";
    
    if (CE->getNumArgs() == 0)
      SS1 << "NULL); \n\t";
    else
      SS1 << paramName.str() << "); \n\t}"; 
    
    // delete the ';' in nextline
    SourceLocation Loc = getNextTokLocStart(CE->getLocEnd());
    Rewrite.ReplaceText(Loc, 1, "");

    // replace the text 
    Rewrite.ReplaceText(CE->getSourceRange(), SS1.str()); 

    // stop to traverse the CallExpr since it has been replaced
    E->setCallExpr(nullptr);
  }

  return true;
}

/// Transform the __CoroC_Chan keyword
bool CoroCRecursiveASTVisitor::VisitCoroCMakeChanExpr(CoroCMakeChanExpr *E) {
  Expr *CE = E->getCapExpr();
  SourceLocation ChanLoc = GetExpansionLoc(Rewrite, E->getLocEnd());
  // Transform to runtime call:
  //  __CoroC_Chan(sizeof type, (expr));

  // replace '<' to '('
  SourceLocation Loc = getNextTokLocStart(ChanLoc);
  Rewrite.ReplaceText(Loc, 1, "(sizeof(");

  // insert '>' before the ',' or '>'
  Token Tok;
  do {
    Tok = getNextTok(Loc);
    Loc = Tok.getLocation();
  } while (Tok.isNot(tok::comma) && Tok.isNot(tok::greater));

  Rewrite.InsertText(Loc, ")");
  Rewrite.ReplaceText(E->getGTLoc(), 1, 
      CE != nullptr ? ")" : ", 0)"); // replace '>' to ')'

  return true;
}

/// Transform the __CoroC_Quit keyword
bool CoroCRecursiveASTVisitor::VisitCoroCQuitStmt(CoroCQuitStmt *S) {
  Expr *RE = S->getReturnExpr();
  SourceLocation QuitLoc = GetExpansionLoc(Rewrite, S->getLocEnd());
  if (RE == nullptr) {
    Rewrite.InsertTextAfterToken(QuitLoc, "(0)");
  } else {
    Rewrite.InsertTextAfterToken(QuitLoc, "(");
    Rewrite.InsertTextAfterToken(RE->getLocEnd(), ")");
  }
  return true;
}

/// Transform the __CoroC_Yield keyword
bool CoroCRecursiveASTVisitor::VisitCoroCYieldStmt(CoroCYieldStmt *S) {
  SourceLocation YieldLoc = GetExpansionLoc(Rewrite, S->getLocEnd());
  Rewrite.InsertTextAfterToken(YieldLoc, "()");
  return true;
}

/// Transform the __CoroC_Select keyword
bool CoroCRecursiveASTVisitor::VisitCoroCSelectStmt(CoroCSelectStmt *S) {
  CompoundStmt *CS = reinterpret_cast<CompoundStmt*>(S->getBody());
  bool hasDef = false;
  CompoundStmt::body_iterator itr = CS->body_begin();
  for (; itr != CS->body_end() && !hasDef; ++itr) {
    CoroCCaseStmt *Case = reinterpret_cast<CoroCCaseStmt*>(*itr);
	if (Case->getChanOpExpr() == nullptr) 
	  hasDef = true;
  }
  
  std::stringstream SS;
  SS << unique_id_generator++;

  SelectHelper *SH = new SelectHelper(Context, Rewrite, SS.str(),
  									  CS->getLocStart(), 
									  CS->getLocEnd(),
									  CS->size(), hasDef);
  SH->GenPrologueAndEpilogue();
  pushSelStk(SH);

  SourceLocation SL = GetExpansionLoc(Rewrite, S->getSelectLoc());
  Rewrite.RemoveText(SourceRange(SL));
  return true;
}

/// Transform the __CoroC_Case / __CoroC_Default
bool CoroCRecursiveASTVisitor::VisitCoroCCaseStmt(CoroCCaseStmt *S) {
  SelectHelper *SH = popSelStk();
  assert (SH != nullptr);
  
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


RewriteCoroC::RewriteCoroC(const std::string &inFile, raw_ostream* OS,
                           DiagnosticsEngine &D, const LangOptions &LOpt) 
                           : Diags(D), LangOpts(LOpt) 
                           , InFileName(inFile), OutFile(OS)
                           , Visitor(nullptr) {
  // TODO
}

void RewriteCoroC::Initialize(ASTContext &C) {
  Context = &C;
  SM = &C.getSourceManager();
  Rewrite.setSourceMgr(C.getSourceManager(), C.getLangOpts());
  Visitor = new CoroCRecursiveASTVisitor(Rewrite, Context);
}

bool RewriteCoroC::HandleTopLevelDecl(DeclGroupRef D) {
  typedef DeclGroupRef::iterator iter;

  for (iter I = D.begin(); I != D.end(); ++I) {
    Visitor->TraverseDecl(*I);  
    // Dump the thunk helpers if any exist
    std::stringstream SS;
    Visitor->DumpThunkHelpers(SS);
    Rewrite.InsertText((*I)->getSourceRange().getBegin(), SS.str());
  }

  return true;
}

void RewriteCoroC::HandleTranslationUnit(ASTContext &C) {
  // print the new file buffer ..
  (*OutFile) << "/* C++ source file auto generated by Clang CoroC rewriter. */\n";
  (*OutFile) << "#include <libcoroc.h>\n";
  (*OutFile) << "#include <__CXX_refcnt_t.hpp>\n\n";

  const RewriteBuffer *RewriteBuf =
    Rewrite.getRewriteBufferFor(SM->getMainFileID());
  (*OutFile) << std::string(RewriteBuf->begin(), RewriteBuf->end());

  // generate the wrapper call to __CoroC_UserMain
  if (Visitor->HasMain()) {
    (*OutFile) << "\n/* wrapper call to __CoroC_UserMain */\n";
    (*OutFile) << "extern \"C\" {\n";
    (*OutFile) << "\tint user_main(int argc, char **argv) {\n\t";
    (*OutFile) << "\t__CoroC_UserMain(argc, argv);\n\t";
    (*OutFile) << "\treturn 0;\n\t}\n";
    (*OutFile) << "}\n/* end of the wrapper call */\n";
  }
}

std::unique_ptr<ASTConsumer>
clang::CreateCoroCRewriter(const std::string &InFile,
                                 raw_ostream *OS,
                                 DiagnosticsEngine &Diags,
                                 const LangOptions &LOpts) {
  return llvm::make_unique<RewriteCoroC>(InFile, OS, Diags, LOpts);
}

