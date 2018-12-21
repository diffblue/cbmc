/*******************************************************************\

Module: Does Remove Const Unit Tests

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Does Remove Const Unit Tests

#ifndef CPROVER__ANALYSES_DOES_REMOVE_CONST_DOES_REMOVE_CONST_UTIL_H
#define CPROVER__ANALYSES_DOES_REMOVE_CONST_DOES_REMOVE_CONST_UTIL_H

#include <analyses/does_remove_const.h>

// This class provides access to private members and functions of
// does_remove_const
class does_remove_const_testt
{
public:
  explicit does_remove_const_testt(does_remove_constt does_remove_const):
    does_remove_const(does_remove_const)
  {}

  bool does_expr_lose_const(const exprt &expr) const
  {
    return does_remove_const.does_expr_lose_const(expr);
  }

  bool is_type_at_least_as_const_as(
    const typet &type_more_const, const typet &type_compare) const
  {
    return does_remove_const.is_type_at_least_as_const_as(
      type_more_const, type_compare);
  }

  bool does_type_preserve_const_correctness(
    const typet *target_type, const typet *source_type) const
  {
    return does_remove_const.does_type_preserve_const_correctness(
      target_type, source_type);
  }

private:
  does_remove_constt does_remove_const;
};

#endif // CPROVER__ANALYSES_DOES_REMOVE_CONST_DOES_REMOVE_CONST_UTIL_H
