/*******************************************************************\

Module: Exception helper utilities

Author: Peter Schrammel, peter.schrammel@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXCEPTION_UTILS_H
#define CPROVER_UTIL_EXCEPTION_UTILS_H

#include "invariant.h"

/// A logic error to be used for OS-related errors (I/O etc)
class system_exceptiont: public std::logic_error
{
public:
  system_exceptiont(
    const std::string &_reason):
    std::logic_error(_reason)
  {
  }
};

/// A logic error to be used for user interface errors
class ui_exceptiont: public std::logic_error
{
public:
  ui_exceptiont(
    const std::string &_reason):
    std::logic_error(_reason)
  {
  }
};

/// A user interface exception with source locations
class input_src_exceptiont: public ui_exceptiont
{
public:
  input_src_exceptiont(
    const source_locationt &_source_location,
    const std::string &_reason):
    ui_exceptiont(_reason),
    source_location(_source_location)
  {
  }
  
  source_locationt source_location;
};

#endif // CPROVER_UTIL_EXCEPTION_UTILS_H
