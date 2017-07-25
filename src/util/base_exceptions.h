/*******************************************************************\

Module: Util base exceptions

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Generic exception types primarily designed for use with invariants.

#ifndef CPROVER_UTIL_BASE_EXCEPTIONS_H
#define CPROVER_UTIL_BASE_EXCEPTIONS_H

#include "util/invariant.h"

class bad_cast_exceptiont:public invariant_failedt
{
public:
  // Normally we'd prefer
  // using invariant_failedt::invariant_failedt;
  // However, this isn't supported on VS2013.

  template <typename... Ts>
  explicit bad_cast_exceptiont(Ts &&...ts):
    invariant_failedt(std::forward<Ts>(ts)...) {}
};

class nullptr_exceptiont:public invariant_failedt
{
public:
  template <typename... Ts>
  explicit nullptr_exceptiont(Ts &&...ts):
    invariant_failedt(std::forward<Ts>(ts)...) {}
};

#endif
