/*******************************************************************\

Module: Nondeterministic boolean helper

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

/// \file
/// Nondeterministic boolean helper

#ifndef CPROVER_UTIL_NONDET_BOOL_H
#define CPROVER_UTIL_NONDET_BOOL_H

#include "std_expr.h"
#include "std_types.h"

/// \param type desired type (C_bool or plain bool)
/// \param source_location source location
/// \return nondet expr of that type
inline exprt
get_nondet_bool(const typet &type, const source_locationt &source_location)
{
  // We force this to 0 and 1 and won't consider
  // other values.
  return typecast_exprt(
    side_effect_expr_nondett(bool_typet(), source_location), type);
}

#endif // CPROVER_UTIL_NONDET_BOOL_H
