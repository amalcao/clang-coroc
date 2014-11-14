//===---  RewriteHelper.h - A simple helper to generate formated code block for the Rewriter.
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
#ifndef _REWRITE_HELPER_H_
#define _REWRITE_HELPER_H_

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Attr.h"
#include "clang/AST/ParentMap.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/APInt.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <sstream>
#include <memory>

namespace ict {
 
  /// \brief Return true if this character is non-new-line whitespace:
  /// ' ', '\\t', '\\f', '\\v', '\\r'.
  static bool isWhitespace(unsigned char c) {
    switch (c) {
    case ' ':
    case '\t':
    case '\f':
    case '\v':
    case '\r':
      return true;
    default:
      return false;
    }
  }

  /// \brief The RewriteHepler -
  class RewriteHelper {
    typedef RewriteHelper& (*RewriteHelperOperator) (RewriteHelper&);

    clang::Rewriter& Rewrite;

    const char* Indentation; // the indent str for each line
    std::string CurLine; // pointer to current line

    void clear() { CurLine = ""; }

    void dump(std::string& Output, llvm::StringRef& Indent) {
      llvm::StringRef Str(CurLine.c_str());

      // If the last line is end with an `Endl'
      bool cleanInsert = Str.endswith("\n");

      llvm::SmallVector<llvm::StringRef, 8> lines;
      Str.split(lines, "\n");

      // print all the buffer into one string and then output to rewriter.
      unsigned e = lines.size();
      if (cleanInsert) e--; // NOTE: split will add the last empty line, so we'd better ignore it!

      for (unsigned i = 0; i != e; ++i) {
        // the first line will insert into the orignal position,
        // so it will share the indentation with orignal line, ignore padding..
        if (i != 0) Output += Indent.str();
        Output += lines[i].str();
        if (i < e-1) Output += "\n";
      }

      // add the indentation for the orignal position for Loc!!
      if (cleanInsert) {
        Output += "\n";
        Output += Indent.str();
      }

      // clear the current LineSet in order to re-use it
      clear();
    }
    
    /// Get the indentaion (number of space) of the line 
    /// which contains the current source location (Loc).
    void getIndentaionOfLine(clang::SourceLocation Loc,
                             llvm::StringRef &Indent) {
      using namespace clang;

      SourceManager& SourceMgr = Rewrite.getSourceMgr();

      std::pair<FileID,unsigned> V = SourceMgr.getDecomposedLoc(Loc);

      StringRef MB = SourceMgr.getBufferData(V.first);
      unsigned LineNo = SourceMgr.getLineNumber(V.first, V.second) - 1;

      const SrcMgr::ContentCache *
        Content = SourceMgr.getSLocEntry(V.first).getFile().getContentCache();

      // Find where the line start.
      unsigned LineOff = Content->SourceLineCache[LineNo];
      unsigned i = LineOff;
      while (isWhitespace(MB[i])) ++i;
      
      Indent = MB.substr(LineOff, i-LineOff);
      return;
    }

  public:
    RewriteHelper(clang::Rewriter *_Rewrite, const char* _Indent = "  ") 
      : Rewrite(*_Rewrite), Indentation(_Indent) { }

    const char* getDefaultIndent() const { return Indentation; }

    /// Insert text before or after the given source locarion.
    bool InsertText(clang::SourceLocation Loc, bool InsertAfter=true) {
      llvm::StringRef Indent;
      std::string LineBuffer;      
      getIndentaionOfLine(Loc, Indent);

      // dump all stored lines into LineBuffer
      dump(LineBuffer, Indent);

      // at last, output to rewriter's buffer
      return Rewrite.InsertText(Loc, LineBuffer.c_str(), InsertAfter);
    }
    
    /// Replace the text in given source location with the new text.
    bool ReplaceText(clang::SourceRange SR) {
      llvm::StringRef Indent;
      std::string LineBuffer;      
      getIndentaionOfLine(SR.getBegin(), Indent);
      dump(LineBuffer, Indent);
      return Rewrite.ReplaceText(SR, LineBuffer.c_str());
    }

    bool InsertTextAfterToken(clang::SourceLocation Loc) {
      llvm::StringRef Indent;
      std::string LineBuffer;      
      getIndentaionOfLine(Loc, Indent);
      dump(LineBuffer, Indent);
      return Rewrite.InsertTextAfterToken(Loc, LineBuffer.c_str());
    }

#define DEFINE_OUTPUT_OPERATOR(Type) \
    RewriteHelper& operator << (Type e) {   \
      std::stringstream ss;                 \
      ss << e; CurLine += ss.str();         \
      return *this;                         \
    }

    DEFINE_OUTPUT_OPERATOR(unsigned)
    DEFINE_OUTPUT_OPERATOR(unsigned long)
    DEFINE_OUTPUT_OPERATOR(const unsigned long long&)
    DEFINE_OUTPUT_OPERATOR(int)
    DEFINE_OUTPUT_OPERATOR(long)
    DEFINE_OUTPUT_OPERATOR(const long long&)

#undef DEFINE_OUTPUT_OPERATOR

    RewriteHelper& operator << (const std::string& str) {
      CurLine += str; return *this;
    }

    RewriteHelper& operator << (const llvm::APInt &I) {
      CurLine += I.toString(10, false);
      return *this;
    }

    RewriteHelper& operator << (const char *str) {
      CurLine += str; return *this;
    }

    RewriteHelper& operator << (clang::QualType Ty) {
      if (Ty.getTypePtrOrNull() != nullptr) {
        CurLine += Ty.getAsString();
      }
      return *this;
    }

    RewriteHelper& operator << (clang::Stmt* S) {
      CurLine += Rewrite.ConvertToString(S);
      return *this;
    }

    RewriteHelper& operator << (clang::NamedDecl* D) {
      CurLine += D->getNameAsString();
      return *this;
    }

    RewriteHelper& operator << (RewriteHelperOperator Op) {
      return Op(*this);
    }
  }; // class RewriteHelper

  /// \brief Endl -
  /// just like a `std::endl', start a new line and flush the buffer.
  static RewriteHelper& Endl(RewriteHelper& RH) {
    RH << "\n"; return RH;
  }

  static RewriteHelper& Indentation(RewriteHelper& RH) {
    RH << RH.getDefaultIndent(); return RH;
  }

} // namespace ict

#endif // _REWRITE_HELPER_H_
