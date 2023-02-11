/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#include "shadow_memory_util.h"

#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

irep_idt extract_field_name(const exprt &string_expr)
{
  if(string_expr.id() == ID_typecast)
    return extract_field_name(to_typecast_expr(string_expr).op());
  else if(string_expr.id() == ID_address_of)
    return extract_field_name(to_address_of_expr(string_expr).object());
  else if(string_expr.id() == ID_index)
    return extract_field_name(to_index_expr(string_expr).array());
  else if(string_expr.id() == ID_string_constant)
  {
    return string_expr.get(ID_value);
  }
  else
    UNREACHABLE;
}
