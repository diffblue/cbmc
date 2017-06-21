/*******************************************************************\

Module:

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FREER_H
#define CPROVER_UTIL_FREER_H

#include <cstdlib>
#include <utility>

/// A functor wrapping `std::free`. Can be used as the deleter of a unique_ptr
/// to free memory originally allocated by `std::malloc`. This is primarily
/// useful for interfacing with C APIs in a memory-safe way.
/// Note that the approach of using an empty functor as a unique_ptr deleter
/// does not impose any space overhead on the unique_ptr instance, whereas
/// using a function-pointer as the deleter requires the unique_ptr to store
/// this function pointer internally, effectively doubling the size of the
/// object. Therefore, `std::unique_ptr<T, freert>` should be preferred to
/// `std::unique_ptr<T, decltype(&std::free)>`.
struct freert
{
  template <typename T>
  void operator()(T &&t) const
  {
    free(std::forward<T>(t));
  }
};

#endif
