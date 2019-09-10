/*******************************************************************\

Module: Util

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_LAZY_H
#define CPROVER_UTIL_LAZY_H

#include <functional>
#include <util/optional.h>

template <typename valuet>
class lazyt
{
public:
  /// Delay the computation of \p fun to the next time the \c force method
  /// is called.
  static lazyt from_fun(std::function<valuet()> fun)
  {
    return lazyt{std::move(fun)};
  }

  /// Force the computation of the value. If it was already computed,
  /// return the same result.
  valuet force()
  {
    if(value)
      return *value;
    value = evaluation_function();
    return *value;
  }

private:
  optionalt<valuet> value;
  std::function<valuet()> evaluation_function;

  explicit lazyt(std::function<valuet()> fun)
    : evaluation_function(std::move(fun))
  {
  }
};

/// Delay the computation of \p fun to the next time the \c force method
/// is called.
template <typename funt>
auto lazy(funt fun) -> lazyt<decltype(fun())>
{
  return lazyt<decltype(fun())>::from_fun(std::move(fun));
}

#endif // CPROVER_UTIL_LAZY_H
