/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_PROGRAMS_ADJUST_FLOAT_EXPRESSIONS_H
#define CPROVER_GOTO_PROGRAMS_ADJUST_FLOAT_EXPRESSIONS_H

#include <goto-programs/goto_functions.h>

class exprt;
class namespacet;
class goto_modelt;

/// Adjust floating point subexpressions in the passed \p expr with the rounding
/// mode from the \p ns. \see adjust_float_expressions(exprt &,
/// const namespacet &)
void adjust_float_expressions(
  exprt &expr,
  const namespacet &ns);

/// Replaces arithmetic operations and typecasts involving floating point
/// numbers with their equivalent `floatbv` version, for example a plus
/// expression (`ID_plus`) turns into a floatbv_plus expression
/// (`ID_floatbv_plus`). These versions of the operators hold the current
/// rounding mode as an additional operand, which affects how these expressions
/// have to be evaluated. (Note that these floating point versions of arithmetic
/// operators do not have corresponding \ref exprt classes at the moment).
///
/// \param expr: The expression to adjust
/// \param rounding_mode: The rounding mode to set on floating point
///   subexpressions of this expression.
void adjust_float_expressions(exprt &expr, const exprt &rounding_mode);

/// Adjust floating point expressions in the body of a given function.
/// \see adjust_float_expressions(exprt &, namespacet &)
/// \see adjust_float_expressions(exprt &, const exprt &)
void adjust_float_expressions(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns);

/// Adjust float expressions in all goto function bodies.
/// \see adjust_float_expressions(
///   goto_functionst::goto_functiont &, const namespacet &)
void adjust_float_expressions(
  goto_functionst &goto_functions,
  const namespacet &ns);

/// Adjust float expressions in a given goto_model.
/// \see adjust_float_expressions(goto_functionst &, const namespacet &)
void adjust_float_expressions(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_ADJUST_FLOAT_EXPRESSIONS_H
