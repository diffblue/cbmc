/*******************************************************************\

Module: Util

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_NODISCARD_H
#define CPROVER_UTIL_NODISCARD_H

#if __has_cpp_attribute(nodiscard)
#  ifdef __clang__
#    pragma GCC diagnostic ignored "-Wc++1z-extensions"
#  endif
// NOLINTNEXTLINE(whitespace/braces)
#  define NODISCARD [[nodiscard]]
#elif __has_cpp_attribute(gnu::warn_unused_result)
// NOLINTNEXTLINE(whitespace/braces)
#  define NODISCARD [[gnu::warn_unused_result]]
#else
#  define NODISCARD
#endif

#endif // CPROVER_UTIL_NODISCARD_H
