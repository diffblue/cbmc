/*******************************************************************\

Module: util

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_THROW_WITH_NESTED_H
#define CPROVER_UTIL_THROW_WITH_NESTED_H

#include <exception>

#ifdef _MSC_VER
#include <stdexcept>
// TODO(tkiley): Nested exception logging not supported on windows due to a bug
// TODO(tkiley): in MSVC++ Compiler (diffblue/cbmc#2104):
// TODO(tkiley): https://blogs.msdn.microsoft.com/vcblog/2016/01/22/vs-2015-update-2s-stl-is-c17-so-far-feature-complete

#define DISABLE_NESTED_EXCEPTIONS

class non_nested_exception_support : public std::runtime_error
{
public:
  non_nested_exception_support()
    : std::runtime_error("Nested exception printing not supported on Windows")
  {
  }
};

#endif

template <class T>
#ifdef __GNUC__
__attribute__((noreturn))
#endif
void util_throw_with_nested(T &&t)
{
#ifndef DISABLE_NESTED_EXCEPTIONS
  std::throw_with_nested(t);
#else
  throw t;
#endif
}

template <class E>
void util_rethrow_if_nested(const E &e)
{
#ifndef DISABLE_NESTED_EXCEPTIONS
//  std::rethrow_if_nested(e);
#else
  // Check we've not already thrown the non_nested_support_exception
//  if(!dynamic_cast<const non_nested_exception_support *>(&e))
//  {
//    throw non_nested_exception_support();
//  }
#endif
}

#endif // CPROVER_UTIL_THROW_WITH_NESTED_H
