/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Constant evaluation of constexpr function calls (N5008 [expr.const])

#ifndef CPROVER_CPP_CPP_CONSTEXPR_EVAL_H
#define CPROVER_CPP_CPP_CONSTEXPR_EVAL_H

#include <util/expr.h>

#include <functional>

class namespacet;
class symbol_table_baset;

/// Evaluate the constexpr function call \p expr (a `side_effect` function
/// call whose arguments are constants) by interpreting the callee's
/// definition: declarations, assignments, `if`, `while`/`do`/`for` loops
/// (bounded), nested constexpr calls ([expr.const]/5).
/// \param expr: the call
/// \param symbol_table: holds the callee's definition (its converted body)
/// \param ns: for simplification
/// \param ensure_definition: called with the identifier of a callee whose
///   definition is not yet available (a queued template specialization,
///   [temp.inst]/5); returns whether it is available afterwards.  May be
///   empty.
/// \return the constant result, or nil when the call cannot be evaluated
exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns,
  const std::function<bool(const irep_idt &)> &ensure_definition = {});

#endif // CPROVER_CPP_CPP_CONSTEXPR_EVAL_H
