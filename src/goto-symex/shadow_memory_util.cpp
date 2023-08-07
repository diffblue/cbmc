/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation Utilities

#include "shadow_memory_util.h"

#include <util/c_types.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/ssa_expr.h>
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

/// If the given type is an array type, then remove the L2 level
/// renaming from its size.
/// \param type Type to be modified
static void remove_array_type_l2(typet &type)
{
  if(to_array_type(type).size().id() != ID_symbol)
    return;

  ssa_exprt &size = to_ssa_expr(to_array_type(type).size());
  size.remove_level_2();
}

void clean_pointer_expr(exprt &expr, const typet &type)
{
  if(
    type.id() == ID_array && expr.id() == ID_symbol &&
    to_array_type(type).size().get_bool(ID_C_SSA_symbol))
  {
    remove_array_type_l2(expr.type());
    exprt original_expr = to_ssa_expr(expr).get_original_expr();
    remove_array_type_l2(original_expr.type());
    to_ssa_expr(expr).set_expression(original_expr);
  }
  if(expr.id() == ID_string_constant)
  {
    expr = address_of_exprt(expr);
    expr.type() = pointer_type(char_type());
  }
  else if(expr.id() == ID_dereference)
  {
    expr = to_dereference_expr(expr).pointer();
  }
  else
  {
    expr = address_of_exprt(expr);
  }
  POSTCONDITION(expr.type().id() == ID_pointer);
}
