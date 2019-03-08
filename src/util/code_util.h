/*******************************************************************\

Module: codet utilities

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_CODE_UTIL_H
#define CPROVER_UTIL_CODE_UTIL_H

#include "std_code.h"

/// Returns a codet that assigns \p expr, of type \p ptr_type, a NULL value, and
/// has source location \p loc.
code_assignt get_null_assignment(
  const exprt &expr,
  const pointer_typet &ptr_type,
  const source_locationt &loc);

#endif // CPROVER_UTIL_CODE_UTIL_H
