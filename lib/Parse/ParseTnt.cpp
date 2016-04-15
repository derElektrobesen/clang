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

///
///     tnt-eval-directive
///       annot_pragma_tnt
///         eval ( <variable> ',' )* <function_call>
///       annot_pragnma_tnt_end
///
static StmtResult parseTnt_eval_Directive(Parser &P) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return StmtError();
}

///
///     tnt-in-directive
///       annot_pragma_tnt
///         in (( <expr> | ?<variable> ) ',')* ( <expr> | ?<variable> )
///       annot_pragma_tnt_end
///
static StmtResult parseTnt_in_Directive(Parser &P) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return StmtError();
}

///
///     tnt-rd-directive
///       annot_pragma_tnt
///         rd (( <expr> | ?<variable> ) ',')* ( <expr> | ?<variable> )
///       annot_pragma_tnt_end
///
static StmtResult parseTnt_rd_Directive(Parser &P) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return StmtError();
}

///
///     tnt-out-directive
///       annot_pragma_tnt
///         out (( <expr> ) ',')* ( <expr> )
///       annot_pragma_tnt_end
///
static StmtResult parseTnt_out_Directive(Parser &P) {
    P.SkipUntil(tok::annot_pragma_tnt_end);
    P.ConsumeToken();
    return StmtError();
}

/// \brief Parsing of Tnt directives.
///
///     tnt-directive:
///       annot_pragma_tnt
///         ( eval | in | rdd | out ) args...
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

  ConsumeToken();
  StmtResult (*parsers[])(Parser &) = {
#define XXX(d) \
    [TntDK_ ## d] = parseTnt_ ## d ## _Directive,
    TNT_DIRECTIVE_KINDS(XXX)
#undef XXX
  };

  return parsers[dir](*this);
}

Parser::DeclGroupPtrTy Parser::HandleTntGlobalDirective() {
  assert(Tok.is(tok::annot_pragma_tnt) && "Not a Tnt directive!");
  Diag(Tok, diag::err_tnt_decl_in_global_scope);
  SkipUntil(tok::annot_pragma_tnt_end);
  ConsumeToken();
  return DeclGroupPtrTy();
}
