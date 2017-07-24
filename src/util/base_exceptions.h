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
  using invariant_failedt::invariant_failedt;
};

class nullptr_exceptiont:public invariant_failedt
{
public:
  using invariant_failedt::invariant_failedt;
};

#endif
