/*******************************************************************\

Module: Nondeterministic boolean helper

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

/// \file
/// Nondeterministic boolean helper

#ifndef CPROVER_UTIL_NONDET_BOOL_H
#define CPROVER_UTIL_NONDET_BOOL_H

#include <util/std_types.h>
#include <util/std_expr.h>

/// \par parameters: Desired type (C_bool or plain bool)
/// \return nondet expr of that type
inline exprt get_nondet_bool(const typet &type)
{
  // We force this to 0 and 1 and won't consider
  // other values.
  return typecast_exprt(side_effect_expr_nondett(bool_typet()), type);
}

#endif // CPROVER_UTIL_NONDET_BOOL_H
