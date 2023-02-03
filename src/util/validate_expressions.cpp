/*******************************************************************\

Module: Validate expressions

Author: Daniel Poetzl

\*******************************************************************/

#include "validate_expressions.h"
#include "validate_helpers.h"

#ifdef REPORT_UNIMPLEMENTED_EXPRESSION_CHECKS
#include <iostream>
#endif

#include "bitvector_expr.h" // IWYU pragma: keep
#include "pointer_expr.h"   // IWYU pragma: keep
#include "ssa_expr.h"

#define CALL_ON_EXPR(expr_type)                                                \
  C<exprt, expr_type>()(expr, std::forward<Args>(args)...)

template <template <typename, typename> class C, typename... Args>
void call_on_expr(const exprt &expr, Args &&... args)
{
  if(expr.id() == ID_equal)
  {
    CALL_ON_EXPR(equal_exprt);
  }
  else if(expr.id() == ID_plus)
  {
    CALL_ON_EXPR(plus_exprt);
  }
  else if(is_ssa_expr(expr))
  {
    CALL_ON_EXPR(ssa_exprt);
  }
  else if(expr.id() == ID_member)
  {
    CALL_ON_EXPR(member_exprt);
  }
  else if(expr.id() == ID_dereference)
  {
    CALL_ON_EXPR(dereference_exprt);
  }
  else if(expr.is_constant())
  {
    CALL_ON_EXPR(constant_exprt);
  }
  else if(expr.id() == ID_if)
  {
    CALL_ON_EXPR(if_exprt);
  }
  else if(expr.id() == ID_update)
  {
    CALL_ON_EXPR(update_exprt);
  }
  else if(expr.id() == ID_overflow_unary_minus)
  {
    CALL_ON_EXPR(unary_minus_overflow_exprt);
  }
  else if(expr.id() == ID_count_leading_zeros)
  {
    CALL_ON_EXPR(count_leading_zeros_exprt);
  }
  else
  {
#ifdef REPORT_UNIMPLEMENTED_EXPRESSION_CHECKS
    std::cerr << "Unimplemented well-formedness check for expression with id: "
              << expr.id_string() std::endl;
#endif

    CALL_ON_EXPR(exprt);
  }
}

/// Check that the given expression is well-formed (shallow checks only, i.e.,
/// subexpressions and its type are not checked)
///
/// The function determines the type `T` of the expression `expr` (by inspecting
/// the `id()` field) and then calls `T::check(expr, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via `DATA_INVARIANT` violations or exceptions.
void check_expr(const exprt &expr, const validation_modet vm)
{
  call_on_expr<call_checkt>(expr, vm);
}

/// Check that the given expression is well-formed, assuming that its
/// subexpression and type have already been checked for well-formedness.
///
/// The function determines the type `T` of the expression `expr` (by inspecting
/// the `id()` field) and then calls `T::validate(expr, ns, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via `DATA_INVARIANT` violations or exceptions.
void validate_expr(
  const exprt &expr,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_expr<call_validatet>(expr, ns, vm);
}

/// Check that the given expression is well-formed (full check, including checks
/// of all subexpressions and the type)
///
/// The function determines the type `T` of the expression `expr` (by inspecting
/// the `id()` field) and then calls `T::validate_full(expr, ns, vm)`.
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via `DATA_INVARIANT` violations or exceptions.
void validate_full_expr(
  const exprt &expr,
  const namespacet &ns,
  const validation_modet vm)
{
  call_on_expr<call_validate_fullt>(expr, ns, vm);
}
