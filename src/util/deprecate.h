/*******************************************************************\

Module:

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_DEPRECATE_H
#define CPROVER_UTIL_DEPRECATE_H

#if __cplusplus >= 201402L
// C++14
#define DEPRECATED(msg) [[deprecated(msg)]]
#elif defined(__GNUC__)
// GCC and GCC compatible compilers
#define DEPRECATED(msg) __attribute__((deprecated(msg)))
#elif defined(_MSC_VER)
// Visual Studio
#define DEPRECATED(msg) __declspec(deprecated(msg))
#else
// Compiler we don't know how to handle or that doesn't have deprecation support
#define DEPRECATED(msg)
#endif

#define SINCE(year, month, day, msg)                                           \
  "deprecated since " #year "-" #month "-" #day "; " msg

#endif // CPROVER_UTIL_DEPRECATE_H
