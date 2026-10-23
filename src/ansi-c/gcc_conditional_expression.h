/*******************************************************************\

Module: Lowering of GCC's `a ? : b` conditional expression

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Lowering of GCC's `a ? : b` (omitted middle operand) conditional
/// expression into an equivalent if-expression.

#ifndef CPROVER_ANSI_C_GCC_CONDITIONAL_EXPRESSION_H
#define CPROVER_ANSI_C_GCC_CONDITIONAL_EXPRESSION_H

#include <util/invariant.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

/// Lower a single GCC `a ? : b` conditional-expression side effect into the
/// equivalent `(a != 0) ? a : b` if-expression.  This drops the guarantee
/// that `a` is evaluated only once, so it is only valid where `a` has no
/// side effects -- i.e. in constant contexts, or after side effects have
/// already been removed (as in goto conversion).
/// \param expr: a side_effect_exprt whose statement is
///   ID_gcc_conditional_expression and which has exactly two operands
/// \return the equivalent if-expression, carrying expr's type and location
inline if_exprt lower_gcc_conditional_expression(const side_effect_exprt &expr)
{
  PRECONDITION(expr.get_statement() == ID_gcc_conditional_expression);
  const binary_exprt &binary = to_binary_expr(expr);
  if_exprt if_expr{
    typecast_exprt::conditional_cast(binary.op0(), bool_typet{}),
    binary.op0(),
    binary.op1(),
    expr.type()};
  if_expr.add_source_location() = expr.source_location();
  return if_expr;
}

/// Recursively rewrite every GCC `a ? : b` conditional-expression side effect
/// in \p expr into `(a != 0) ? a : b` if-expressions.  Only valid in constant
/// contexts, where the once-only evaluation of `a` is immaterial (there are
/// no side effects), so that the simplifier can fold the result.
inline void lower_gcc_conditional_expressions(exprt &expr)
{
  for(auto &op : expr.operands())
    lower_gcc_conditional_expressions(op);

  if(
    expr.id() == ID_side_effect &&
    to_side_effect_expr(expr).get_statement() ==
      ID_gcc_conditional_expression &&
    expr.operands().size() == 2)
  {
    if_exprt if_expr =
      lower_gcc_conditional_expression(to_side_effect_expr(expr));
    expr.swap(if_expr);
  }
}

#endif // CPROVER_ANSI_C_GCC_CONDITIONAL_EXPRESSION_H
