/*******************************************************************\

Module: Evaluate if an expression is consistent with examples

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Evaluate if an expression is consistent with examples

#ifndef CPROVER_GOTO_SYNTHESIZER_CEGIS_EVALUATOR_H
#define CPROVER_GOTO_SYNTHESIZER_CEGIS_EVALUATOR_H

#include "cegis_verifier.h"

/// Evaluator for checking if an expression is consistent with a given set of
/// test cases (positive examples and negative examples).
class cegis_evaluatort
{
public:
  cegis_evaluatort(const exprt &expr, const std::vector<cext> &cexs)
    : checked_expr(expr), cexs(cexs)
  {
  }

  // Evaluate if the expression `checked_expr` is consistent with `cexs`.
  // Return true if `checked_expr` is consistent with all examples.
  bool evaluate();

protected:
  // Recursively evaluate boolean expressions on `cex`.
  // If `is_positive` is set, evaluate on the positive example in `cex`.
  // The positive example is the test collected from the first iteration of
  // loop---the loop_entry valuation.
  bool
  evaluate_rec_bool(const exprt &expr, const cext &cex, const bool is_positive);

  // Recursively evaluate integer expressions on `cex`.
  // If `is_positive` is set, evaluate on the positive example in `cex`.
  // The positive example is the test collected from the first iteration of
  // loop---the loop_entry valuation.
  mp_integer
  evaluate_rec_int(const exprt &expr, const cext &cex, const bool is_positive);

  /// @brief The expression being evaluated.
  const exprt &checked_expr;
  /// @brief The set of examples evaluated against.
  const std::vector<cext> &cexs;
};

#endif // CPROVER_GOTO_SYNTHESIZER_CEGIS_EVALUATOR_H
