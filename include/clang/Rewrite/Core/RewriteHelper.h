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

  template<typename T>
  static void AddToString(std::string& str, T i) {
    std::stringstream ss;
    ss << i;
    str += ss.str();
  }

  /// \brief The RewriteHepler -
  class RewriteHelper {
    typedef RewriteHelper& (*RewriteHelperOperator) (RewriteHelper&);

    clang::Rewriter& Rewrite;

    std::string *CurLine; // pointer to current line
    std::vector<std::string*> LineSet; // store all the lines

    void clear(bool exit = false) {
      // release the unpushed line first
      if (exit && CurLine != nullptr)
        delete CurLine;

      // release all lines stored in the LineSet
      for (std::vector<std::string*>::iterator I = LineSet.begin();
           I != LineSet.end(); ++I) delete *I;
      LineSet.clear();
    }

    void dump(std::string& Output, std::string& Indent) {
      // If the last line is end with an `Endl'
      bool cleanInsert = true;
      // push current line into the buffer
      if (CurLine != nullptr && CurLine->length() > 0) {
        cleanInsert = false;
        LineSet.push_back(CurLine);
        CurLine = nullptr;
      }
      
      // print all the buffer into one string and then output to rewriter.
      for (std::vector<std::string*>::iterator I = LineSet.begin();
           I != LineSet.end(); ++I) {
        // the first line will insert into the orignal position,
        // so it will share the indentation with orignal line, ignore padding..
        if (I != LineSet.begin())
          Output += Indent; // FIXME
        Output += *(*I);
      }

      // add the indentation for the orignal position for Loc!!
      if (cleanInsert) Output += Indent;
      
      // clear the current LineSet in order to re-use it
      clear();
      if (CurLine == nullptr) 
        CurLine = new std::string;
    }
    
    /// Get the indentaion (number of space) of the line 
    /// which contains the current source location (Loc).
    void getIndentaionOfLine(clang::SourceLocation Loc,
                             std::string &Indent) {
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
    RewriteHelper(clang::Rewriter *_Rewrite) 
      : Rewrite(*_Rewrite), CurLine(new std::string) { }
    ~RewriteHelper() { 
      clear(true);
    }

    void endline() {
      assert(CurLine != nullptr);
      (*CurLine) += "\n";
      LineSet.push_back(CurLine);

      CurLine = new std::string;
    }

    unsigned getLineNum() {
      if (CurLine && CurLine->length() > 0)
        return LineSet.size() + 1;
      return LineSet.size();
    }

    /// Insert text before or after the given source locarion.
    bool InsertText(clang::SourceLocation Loc, bool InsertAfter=true) {
      std::string Indent, LineBuffer;      
      getIndentaionOfLine(Loc, Indent);

      // dump all stored lines into LineBuffer
      dump(LineBuffer, Indent);

      // at last, output to rewriter's buffer
      return Rewrite.InsertText(Loc, LineBuffer.c_str(), InsertAfter);
    }
    
    /// Replace the text in given source location with the new text.
    bool ReplaceText(clang::SourceRange SR) {
      std::string Indent, LineBuffer;
      getIndentaionOfLine(SR.getBegin(), Indent);
      dump(LineBuffer, Indent);
      return Rewrite.ReplaceText(SR, LineBuffer.c_str());
    }

    bool InsertTextAfterToken(clang::SourceLocation Loc) {
      std::string Indent, LineBuffer;
      getIndentaionOfLine(Loc, Indent);
      dump(LineBuffer, Indent);
      return Rewrite.InsertTextAfterToken(Loc, LineBuffer.c_str());
    }

    RewriteHelper& operator << (unsigned u) {
      AddToString<unsigned>(*CurLine, u);
      return *this;
    }

    RewriteHelper& operator << (unsigned long ul) {
      AddToString<unsigned long>(*CurLine, ul);
      return *this;
    }

    RewriteHelper& operator << (const unsigned long long& ull) {
      AddToString<const unsigned long long&>(*CurLine, ull);
      return *this;
    }

    RewriteHelper& operator << (int i) {
      AddToString<int>(*CurLine, i);
      return *this;
    }

    RewriteHelper& operator << (long l) {
      AddToString<long>(*CurLine, l);
      return *this;
    }

    RewriteHelper& operator << (const long long& ll) {
      AddToString<const long long&>(*CurLine, ll);
      return *this;
    }

    RewriteHelper& operator << (const llvm::APInt &I) {
      (*CurLine) += I.toString(10, false);
      return *this;
    }

    RewriteHelper& operator << (const std::string& str) {
      (*CurLine) += str; return *this;
    }

    RewriteHelper& operator << (const char *str) {
      (*CurLine) += str; return *this;
    }

    RewriteHelper& operator << (clang::QualType Ty) {
      if (Ty.getTypePtrOrNull() != nullptr) {
        (*CurLine) += Ty.getAsString();
      }
      return *this;
    }

    RewriteHelper& operator << (clang::Stmt* S) {
      (*CurLine) += Rewrite.ConvertToString(S);
      return *this;
    }

    RewriteHelper& operator << (clang::NamedDecl* D) {
      (*CurLine) += D->getNameAsString();
      return *this;
    }

    RewriteHelper& operator << (RewriteHelperOperator Op) {
      return Op(*this);
    }
  }; // class RewriteHelper

  /// \brief Endl -
  /// just like a `std::endl', start a new line and flush the buffer.
  static RewriteHelper& Endl(RewriteHelper& RH) {
    RH.endline(); return RH;
  }

  static RewriteHelper& Indentation(RewriteHelper& RH) {
    RH << "  "; return RH;
  }

} // namespace ict

#endif // _REWRITE_HELPER_H_
