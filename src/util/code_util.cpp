/*******************************************************************\

Module: codet utilities

Author: Diffblue Ltd.

\*******************************************************************/

#include "code_util.h"

code_assignt get_null_assignment(
  const exprt &expr,
  const pointer_typet &ptr_type,
  const source_locationt &loc)
{
  code_assignt code{expr, null_pointer_exprt{ptr_type}};
  code.add_source_location() = loc;
  return code;
}
