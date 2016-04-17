//===--- ParseTnt.cpp - Tnt directives parsing ---------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file implements parsing of all Tnt directives and clauses.
///
//===----------------------------------------------------------------------===//

#include "RAIIObjectsForParser.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/StmtOpenMP.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Scope.h"
#include "llvm/ADT/PointerIntPair.h"

using namespace clang;

#define TNT_DIRECTIVE_KINDS(_) \
  _(in) \
  _(out) \
  _(rd) \
  _(eval)

namespace {
  enum TntDirectiveKind {
#define XXX(d) TntDK_ ## d,
    TNT_DIRECTIVE_KINDS(XXX)
#undef XXX

    TntDK_unknown
  };

  struct TokenReplacement {
    std::string FuncName;
    uint64_t ArrLen;
    SmallVector<Token, 4> Args;

    TokenReplacement(std::string const& FuncName, uint64_t ArrLen)
      : FuncName(FuncName), ArrLen(ArrLen) {}
    TokenReplacement() : ArrLen(0) {}
  };
} // namespace

static TntDirectiveKind getTntDirectiveKind(Parser &P) {
  auto Tok = P.getCurToken();
  if (Tok.isAnnotation())
    return TntDK_unknown;

  return llvm::StringSwitch<TntDirectiveKind>(P.getPreprocessor().getSpelling(Tok))
#define XXX(d) .Case(#d, TntDK_ ## d)
        TNT_DIRECTIVE_KINDS(XXX)
#undef XXX
        .Default(TntDK_unknown);
}

bool Parser::ParseTntSimpleVarList(SmallVectorImpl<Expr *> &VarList) {
  return true;
}

static const char *tntDirectiveToStr(TntDirectiveKind d) {
  switch (d) {
#define XXX(d) \
    case TntDK_ ## d    : return #d;
    TNT_DIRECTIVE_KINDS(XXX)
#undef XXX
    case TntDK_unknown  : return "unknown";
    default             : assert(!"Invalid TntDirectiveKind!");
  };

  return nullptr;
}

static std::string mkFuncName(std::string const& name, bool is_formal) {
  return "__tnt_" + name + (is_formal ? "_formal" : "") + "_type_converter";
}

static std::string typeToFuncName(QualType const& type, bool is_formal, uint64_t *arr_size = nullptr, bool under_recursion = false) {
  if (type->isScalarType()) {
    if (type->isCharType())
      return mkFuncName("char", is_formal);
    if (type->isIntegerType())
      return mkFuncName("int", is_formal);
    if (type->isRealFloatingType())
      return mkFuncName("double", is_formal);

    if (type->isPointerType()) {
      const PointerType *ptr_t = dyn_cast<PointerType>(type);
      if (!ptr_t)
        return std::string();

      QualType pointee = ptr_t->getPointeeType();
      if (pointee->isCharType())
        return mkFuncName("char_ptr", is_formal); // only c-strings are supported

      return std::string();
    }

    return std::string();
  } else if (under_recursion)
    return std::string(); // pointers on pointers are not supported

  if (type->isConstantArrayType()) {
    const ConstantArrayType* arr_t = dyn_cast<ConstantArrayType>(type);
    if (!arr_t)
      return std::string();
    if (arr_size)
      *arr_size = arr_t->getSize().getZExtValue();
    return typeToFuncName(arr_t->getElementType(), is_formal, nullptr, true);
  }

  return std::string();
}

namespace clang {

class TntParser {
private:
  Parser &P;

public:
  TntParser(Parser &P)
    : P(P)
  {}

  bool isPossiblyFormal() {
    Token Tok = P.getCurToken();
    return Tok.is(tok::question); // first token is '?'
  }

  StmtResult processPragma() {
    Parser::TentativeParsingAction TPA(P);
    P.ConsumeToken(); // annot_pragma_tnt

    TntDirectiveKind dir = getTntDirectiveKind(P);
    if (dir == TntDK_unknown) {
      P.Diag(P.getCurToken(), diag::err_tnt_unknown_directive);
      P.SkipUntil(tok::annot_pragma_tnt_end);
      P.ConsumeToken();
      TPA.Commit();
      return StmtError();
    }

    // don't consume pragma type identifier
    SmallVector<TokenReplacement, 16> repl;
    if (!parsePragmaTokens(repl, dir)) {
      TPA.Commit();
      return StmtError();
    }

    TPA.Commit();

    return StmtEmpty();
  }

  bool parsePragmaTokens(SmallVectorImpl<TokenReplacement> &replace_with, TntDirectiveKind kind) {
    replace_with.clear();

    assert(kind != TntDK_unknown);
    bool accept_formals = (kind == TntDK_in || kind == TntDK_rd);

    Token Tok = P.getCurToken();
    SmallVector<TokenReplacement, 16> Replacement;

    Preprocessor &PP = P.getPreprocessor();

    bool formal_found = false;
    bool correct = true;
    bool is_first_iter = true;

    auto _abort = [&correct] (Parser::TentativeParsingAction &TPA) {
      TPA.Commit();
      correct = false;
    };


    while (Tok.isNot(tok::annot_pragma_tnt_end)) {
      Token ExprBoundary;
      ExprBoundary.startToken();
      ExprBoundary.setKind(tok::l_brace);
      ExprBoundary.setLocation(Tok.getLocation());
      PP.EnterToken(ExprBoundary); // enter brace after comma or annot_pragma_tnt
                                   // to devide expressions

      PP.DumpToken(P.getCurToken());
      llvm::errs() << "\n";

      if (is_first_iter)
        assert(Tok.is(tok::identifier));
      else
        assert(Tok.is(tok::r_brace));

      P.ConsumeAnyToken();
      is_first_iter = false;

      Tok = P.getCurToken();
      if (Tok.is(tok::annot_pragma_tnt_end))
        break;

      Parser::TentativeParsingAction TPA(P);
      P.ConsumeBrace();

      bool is_formal = isPossiblyFormal();
      Token formalTok = P.getCurToken();
      if (is_formal && !accept_formals) {
        P.Diag(formalTok, diag::err_tnt_unsupported_formal);
        _abort(TPA);
        break;
      } else if (is_formal) {
        Tok = P.getCurToken();
        assert(Tok.is(tok::question));
        P.ConsumeToken();
      }

      auto expr = P.ParseAssignmentExpression();
      if (expr.isInvalid()) {
        // error message already shawn
        _abort(TPA);
        break;
      }

      Tok = P.getCurToken();
      if (is_formal) {
        if (!isa<DeclRefExpr>(expr.get())) {
          P.Diag(formalTok, diag::err_tnt_invalid_formal);
          _abort(TPA);
          break;
        }

        const DeclRefExpr *decl_ref = dyn_cast<DeclRefExpr>(expr.get());
        if (!isa<VarDecl>(decl_ref->getDecl())) { // TODO: not only variables can be formal
          P.Diag(formalTok, diag::err_tnt_invalid_formal);
          _abort(TPA);
          break;
        }

        if (decl_ref->getType().isConstQualified()) {
          P.Diag(formalTok, diag::err_tnt_const_formal);
          _abort(TPA);
          break;
        }
      }

      uint64_t size = 0;
      std::string func_name = typeToFuncName(expr.get()->getType(), is_formal, &size);
      if (!func_name.size()) {
        P.Diag(Tok, diag::err_tnt_unsupported_type) << expr.get()->getType().getAsString();
        _abort(TPA);
        break;
      }

      if (Tok.isNot(tok::annot_pragma_tnt_end) && Tok.isNot(tok::comma)) {
        P.Diag(Tok, diag::err_expected_expression); // TODO: print correct message here
        _abort(TPA);
        break;
      }

      if (Tok.isNot(tok::annot_pragma_tnt_end)) {
        ExprBoundary.startToken();
        ExprBoundary.setKind(tok::r_brace);
        ExprBoundary.setLocation(Tok.getLocation());
        PP.EnterToken(ExprBoundary); // add brace AFTER comma
      }

      TPA.Revert();
      P.ConsumeBrace(); // consume l_brace

      TokenReplacement repl(func_name, size);
      Tok = P.getCurToken();
      assert(P.ConsumeAndStoreUntil(tok::r_brace, tok::annot_pragma_tnt_end, repl.Args, /*StopOnSemi*/true, /*ConsumeFinalToken*/false)
          && "Achtung! r_brace not found in stream!");

      repl.Args.pop_back(); // remove comma from args list

      if (is_formal) {
        Token l_paren;
        l_paren.startToken();
        l_paren.setKind(tok::l_paren);
        l_paren.setLocation(Tok.getLocation());
        repl.Args.insert(repl.Args.begin(), l_paren);

        Token amp;
        amp.startToken();
        amp.setKind(tok::amp);
        amp.setLocation(Tok.getLocation());
        repl.Args.insert(repl.Args.begin(), amp);

        Token r_paren;
        r_paren.startToken();
        r_paren.setKind(tok::r_paren);
        r_paren.setLocation(repl.Args.back().getLocation());
        repl.Args.push_back(r_paren);
      }

      replace_with.push_back(repl);

      // XXX: Don't consume r_brace!!!
      Tok = P.getCurToken();
    }

    if (Tok.isNot(tok::annot_pragma_tnt_end))
      P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken(); // consume annot_pragma_tnt_end

    return correct;

  }
};

} // namespace clang

/// \brief Parsing of Tnt directives.
///
///     tnt-directive:
///       annot_pragma_tnt
///         ( eval | in | rd | out ) args...
///       annot_pragma_tnt_end
///
StmtResult Parser::ParseTntDirective() {
  assert(Tok.is(tok::annot_pragma_tnt) && "Not a Tnt directive!");
  TntParser parser(*this);
  return parser.processPragma();
}

Parser::DeclGroupPtrTy Parser::HandleTntGlobalDirective() {
  assert(Tok.is(tok::annot_pragma_tnt) && "Not a Tnt directive!");
  Diag(Tok, diag::err_tnt_decl_in_global_scope);
  SkipUntil(tok::annot_pragma_tnt_end);
  ConsumeToken();
  return DeclGroupPtrTy();
}
