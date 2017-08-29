/*******************************************************************\

Module: Wrap the designated entry point into a while(true) loop.

Author: Diffblue Limited (c) 2017

Date: August 2017

\*******************************************************************/

/// \file
/// Wrap the designated entry point into a while(true) loop.

#include "wrap_entry_point.h"

// Build and return a while(true) statement nesting the function call
// passed as a parameter.
code_whilet wrap_entry_point_in_while(code_function_callt &call_main)
{
  exprt true_expr;
  code_whilet while_expr;
  true_expr.make_true();
  while_expr.cond() = true_expr;
  while_expr.body() = call_main;

  return while_expr;
}
