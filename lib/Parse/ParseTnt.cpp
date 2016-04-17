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
  };
} // namespace

static TntDirectiveKind getTntDirectiveKind(Parser &P) {
  auto Tok = P.getCurToken();
  if (Tok.isAnnotation())
    return TntDK_unknown;

  llvm::errs() << P.getPreprocessor().getSpelling(Tok);
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

static std::string mkFuncName(std::string const& name) {
  return "__tnt_" + name + "_type_converter";
}

static std::string typeToFuncName(QualType const& type, uint64_t *arr_size = nullptr, bool under_recursion = false) {
  if (type->isScalarType()) {
    if (type->isCharType())
      return mkFuncName("char");
    if (type->isIntegerType())
      return mkFuncName("int");
    if (type->isRealFloatingType())
      return mkFuncName("double");

    if (type->isPointerType()) {
      const PointerType *ptr_t = dyn_cast<PointerType>(type);
      if (!ptr_t)
        return std::string();

      QualType pointee = ptr_t->getPointeeType();
      if (pointee->isCharType())
        return mkFuncName("char_ptr"); // only c-strings are supported

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
    return typeToFuncName(arr_t->getElementType(), nullptr, true);
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

  ///
  ///     tnt-eval-directive
  ///       annot_pragma_tnt
  ///         eval ( <variable> ',' )* <function_call>
  ///       annot_pragnma_tnt_end
  ///
  bool parseTnt_eval_Directive(SmallVectorImpl<TokenReplacement> &replace_with) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return false;
  }

  ///
  ///     tnt-in-directive
  ///       annot_pragma_tnt
  ///         in (( <expr> | ?<variable> ) ',')* ( <expr> | ?<variable> )
  ///       annot_pragma_tnt_end
  ///
  bool parseTnt_in_Directive(SmallVectorImpl<TokenReplacement> &replace_with) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return false;
  }

  ///
  ///     tnt-rd-directive
  ///       annot_pragma_tnt
  ///         rd (( <expr> | ?<variable> ) ',')* ( <expr> | ?<variable> )
  ///       annot_pragma_tnt_end
  ///
  bool parseTnt_rd_Directive(SmallVectorImpl<TokenReplacement> &replace_with) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return false;
  }

  ///
  ///     tnt-out-directive
  ///       annot_pragma_tnt
  ///         out (( <expr> ) ',')* ( <expr> )
  ///       annot_pragma_tnt_end
  ///
  bool parseTnt_out_Directive(SmallVectorImpl<TokenReplacement> &replace_with) {
    replace_with.clear();

    Token Tok = P.getCurToken();
    SmallVector<TokenReplacement, 16> Replacement;

    Preprocessor &PP = P.getPreprocessor();

    bool correct = true;
    while (Tok.isNot(tok::annot_pragma_tnt_end)) {
      Token ExprBoundary;
      ExprBoundary.startToken();
      ExprBoundary.setKind(tok::l_brace);
      ExprBoundary.setLocation(Tok.getLocation());
      PP.EnterToken(ExprBoundary); // enter brace after comma or annot_pragma_tnt
                                   // to devide expressions

      assert(Tok.isOneOf(tok::r_brace, tok::annot_pragma_tnt));
      P.ConsumeAnyToken();
      Tok = P.getCurToken();
      if (Tok.is(tok::annot_pragma_tnt_end))
        break;

      Parser::TentativeParsingAction TPA(P);
      P.ConsumeBrace();

      auto expr = P.ParseAssignmentExpression();
      if (expr.isInvalid()) {
        // error message already shawn
        TPA.Commit();
        correct = false;
        break;
      }

      Tok = P.getCurToken();
      uint64_t size = 0;
      std::string func_name = typeToFuncName(expr.get()->getType(), &size);
      if (!func_name.size()) {
        P.Diag(Tok, diag::err_tnt_unsupported_type) << expr.get()->getType().getAsString();
        TPA.Commit();
        correct = false;
        break;
      }

      if (Tok.isNot(tok::annot_pragma_tnt_end) && Tok.isNot(tok::comma)) {
        P.Diag(Tok, diag::err_expected_expression); // TODO: print correct message here
        TPA.Commit();
        correct = false;
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
      assert(P.ConsumeAndStoreUntil(tok::r_brace, tok::annot_pragma_tnt_end, repl.Args, /*StopOnSemi*/true, /*ConsumeFinalToken*/false)
          && "Achtung! r_brace not found in stream!");

      repl.Args.pop_back(); // remove comma from args list
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

  ConsumeToken();

  TntDirectiveKind dir = getTntDirectiveKind(*this);
  if (dir == TntDK_unknown) {
    Diag(Tok, diag::err_tnt_unknown_directive);
    SkipUntil(tok::annot_pragma_tnt_end);
    ConsumeToken();
    return StmtError();
  }

  TntParser parser(*this);
  std::function<bool(SmallVectorImpl<TokenReplacement>&)> parsers[] = {
#define XXX(d) \
    [TntDK_ ## d] = [&parser] (SmallVectorImpl<TokenReplacement> &tokens) { return parser.parseTnt_ ## d ## _Directive(tokens); },
    TNT_DIRECTIVE_KINDS(XXX)
#undef XXX
  };

  SmallVector<TokenReplacement, 16> tokens;
  bool res = parsers[dir](tokens);
  if (!res)
    return StmtError();
}

Parser::DeclGroupPtrTy Parser::HandleTntGlobalDirective() {
  assert(Tok.is(tok::annot_pragma_tnt) && "Not a Tnt directive!");
  Diag(Tok, diag::err_tnt_decl_in_global_scope);
  SkipUntil(tok::annot_pragma_tnt_end);
  ConsumeToken();
  return DeclGroupPtrTy();
}
