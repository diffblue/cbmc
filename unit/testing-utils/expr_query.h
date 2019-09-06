/*******************************************************************\

Module: Unit test utilities

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Helper class for querying expressions
/// Throw CATCH exceptions when the query fails.

#ifndef CPROVER_TESTING_UTILS_EXPR_QUERY_H
#define CPROVER_TESTING_UTILS_EXPR_QUERY_H

#include <testing-utils/use_catch.h>
#include <util/expr.h>
#include <util/expr_cast.h>

/// Wrapper for optionalt<exprt> with useful method for queries to be used in
/// unit tests.
template <typename T = exprt>
class expr_queryt
{
  static_assert(
    std::is_base_of<exprt, T>::value,
    "T should inherit from exprt");

public:
  explicit expr_queryt(T e) : value(std::move(e))
  {
  }

  template <typename targett>
  expr_queryt<targett> as() const
  {
    auto result = expr_try_dynamic_cast<targett>(static_cast<exprt>(value));
    REQUIRE(result);
    return expr_queryt<targett>(*result);
  }

  expr_queryt<exprt> operator[](const std::size_t i) const
  {
    REQUIRE(value.operands().size() > i);
    return expr_queryt<exprt>(value.operands()[i]);
  }

  T get() const
  {
    return value;
  }

private:
  T value;
};

inline expr_queryt<exprt> make_query(exprt e)
{
  return expr_queryt<exprt>(std::move(e));
}

#endif // CPROVER_TESTING_UTILS_EXPR_QUERY_H
