/*******************************************************************\

 Module: typedef for optional class template. To be replaced with
 std::optional once C++17 support is enabled

 Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_OPTIONAL_H
#define CPROVER_UTIL_OPTIONAL_H

#if defined __clang__
  #pragma clang diagnostic push ignore "-Wall"
  #pragma clang diagnostic push ignore "-Wpedantic"
#elif defined __GNUC__
  #pragma GCC diagnostic push ignore "-Wall"
  #pragma GCC diagnostic push ignore "-Wpedantic"
#elif defined _MSC_VER
  #pragma warning(push)
#endif
#include <nonstd/optional.hpp>
#if defined  __clang__
  #pragma clang diagnostic pop
  #pragma clang diagnostic pop
#elif defined  __GNUC__
  #pragma GCC diagnostic pop
  #pragma GCC diagnostic pop
#elif defined _MSC_VER
  #pragma warning(pop)
#endif

// Swap for std::optional when switching to C++17
template<typename T>
using optionalt=nonstd::optional<T>; // NOLINT template typedef

typedef nonstd::bad_optional_access bad_optional_accesst;

using nonstd::nullopt;

#endif // CPROVER_UTIL_OPTIONAL_H
