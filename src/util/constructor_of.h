/*******************************************************************\

Module: constructor_of

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_CONSTRUCTOR_OF_H
#define CPROVER_UTIL_CONSTRUCTOR_OF_H

#include <utility>

/// A type of functor which wraps around the set of constructors of a type.
/// \tparam constructedt: The type which this functor constructs.
template <typename constructedt>
class constructor_oft final
{
public:
  template <typename... argumentst>
  constructedt operator()(argumentst &&... arguments)
  {
    return constructedt{std::forward<argumentst>(arguments)...};
  }
};

/// \tparam constructedt: A type for construction.
/// \brief Returns a functor which constructs type `constructedt`.
template <typename constructedt>
constexpr constructor_oft<constructedt> constructor_of()
{
  return {};
}

#endif // CPROVER_UTIL_CONSTRUCTOR_OF_H
