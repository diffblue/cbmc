/*******************************************************************\

Module: Callback object for dereference_rec

Author: Owen Jones, owen.jones@diffblue.com

\*******************************************************************/

/// \file
/// Callback object for dereference_rec

#include "single_value_set_dereference_callback.h"

#include <util/symbol_table.h>

const symbolt *
single_value_set_dereference_callbackt::get_or_create_failed_symbol(
  const exprt &expr)
{
  get_or_create_failed_symbol_called = true;
  return nullptr;
}

void single_value_set_dereference_callbackt::get_value_set(
  const exprt &expr,
  value_setst::valuest &value_set) const
{
  if(expr == query_expr)
  {
    get_value_set_called_with_right_query_expr = true;
    value_set = return_values;
  }
  else
  {
    get_value_set_called_with_wrong_query_expr = true;
    value_set = value_setst::valuest();
  }
}

bool single_value_set_dereference_callbackt::used_correctly()
{
  return !get_or_create_failed_symbol_called &&
         !get_value_set_called_with_wrong_query_expr;
}
