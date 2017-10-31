/*******************************************************************\

Module: exprt conversion functions

Author: Diffblue ltd. All Rights Reserved

\*******************************************************************/

/// \file
/// Abstraction Refinement Loop

#ifndef CPROVER_SOLVERS_REFINEMENT_EXPR_CAST_H
#define CPROVER_SOLVERS_REFINEMENT_EXPR_CAST_H

#include <util/optional.h>

/// Convert exprt to a specific type. Remove empty optional if
/// conversion cannot be performed
/// Generic case doesn't exist, specialize for different types accordingly
/// TODO: this should go to util
template<typename T>
struct expr_cast_implt final { };

template<>
struct expr_cast_implt<mp_integer> final
{
  optionalt<mp_integer> operator()(const exprt &expr) const
  {
    mp_integer out;
    if(to_integer(expr, out))
      return {};
    return out;
  }
};

template<>
struct expr_cast_implt<std::size_t> final
{
  optionalt<std::size_t> operator()(const exprt &expr) const
  {
    if(const auto tmp=expr_cast_implt<mp_integer>()(expr))
      if(tmp->is_long() && *tmp>=0)
        return tmp->to_long();
    return {};
  }
};

template <>
struct expr_cast_implt<refined_string_exprt> final
{
  optionalt<refined_string_exprt> operator()(const exprt &expr) const
  {
    if(is_refined_string_type(expr.type()))
      return to_string_expr(expr);
    return {};
  }
};

template<typename T>
optionalt<T> expr_cast(const exprt& expr)
{ return expr_cast_implt<T>()(expr); }

template<typename T>
T expr_cast_v(const exprt &expr)
{
  const auto maybe=expr_cast<T>(expr);
  INVARIANT(maybe, "Bad conversion");
  return *maybe;
}

#endif // CPROVER_SOLVERS_REFINEMENT_EXPR_CAST_H
