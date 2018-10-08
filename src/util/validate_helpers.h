/*******************************************************************\

Module: Goto program validation helper templates

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATE_HELPERS_H
#define CPROVER_UTIL_VALIDATE_HELPERS_H

#include <type_traits>

class namespacet;
enum class validation_modet;

template <typename Base, typename T>
struct call_checkt
{
  static_assert(std::is_base_of<Base, T>::value, "");

  void operator()(const Base &base, const validation_modet vm)
  {
    T::check(base, vm);
  }
};

template <typename Base, typename T>
struct call_validatet
{
  static_assert(std::is_base_of<Base, T>::value, "");

  void
  operator()(const Base &base, const namespacet &ns, const validation_modet vm)
  {
    T::validate(base, ns, vm);
  }
};

template <typename Base, typename T>
struct call_validate_fullt
{
  static_assert(std::is_base_of<Base, T>::value, "");

  void
  operator()(const Base &base, const namespacet &ns, const validation_modet vm)
  {
    T::validate_full(base, ns, vm);
  }
};

#endif /* CPROVER_UTIL_VALIDATE_HELPERS_H */
