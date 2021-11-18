/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/expr_util.h>
#include <util/source_location.h>
#include <util/std_expr.h>

void goto_convertt::convert_function_call(
  const code_function_callt &function_call,
  goto_programt &dest,
  const irep_idt &mode)
{
  do_function_call(
    function_call.lhs(),
    function_call.function(),
    function_call.arguments(),
    dest,
    mode);
}

void goto_convertt::do_function_call(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest,
  const irep_idt &mode)
{
  // make it all side effect free

  exprt new_lhs=lhs,
        new_function=function;

  exprt::operandst new_arguments=arguments;

  if(!new_lhs.is_nil())
    clean_expr(new_lhs, dest, mode);

  clean_expr(new_function, dest, mode);

  for(auto &new_argument : new_arguments)
    clean_expr(new_argument, dest, mode);

  // split on the function

  if(new_function.id()==ID_if)
  {
    do_function_call_if(
      new_lhs, to_if_expr(new_function), new_arguments, dest, mode);
  }
  else if(new_function.id()==ID_symbol)
  {
    do_function_call_symbol(
      new_lhs, to_symbol_expr(new_function), new_arguments, dest, mode);
  }
  else if(new_function.id() == ID_null_object)
  {
  }
  else if(new_function.id()==ID_dereference ||
          new_function.id()=="virtual_function")
  {
    do_function_call_other(new_lhs, new_function, new_arguments, dest);
  }
  else
  {
    INVARIANT_WITH_DIAGNOSTICS(
      false,
      "unexpected function argument",
      new_function.id(),
      function.find_source_location());
  }
}

void goto_convertt::do_function_call_if(
  const exprt &lhs,
  const if_exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest,
  const irep_idt &mode)
{
  // case split

  //    c?f():g()
  //--------------------
  // v: if(!c) goto y;
  // w: f();
  // x: goto z;
  // y: g();
  // z: ;

  // do the v label
  goto_programt tmp_v;
  goto_programt::targett v = tmp_v.add(goto_programt::make_incomplete_goto(
    boolean_negate(function.cond()), function.cond().source_location()));

  // do the x label
  goto_programt tmp_x;
  goto_programt::targett x =
    tmp_x.add(goto_programt::make_incomplete_goto(true_exprt()));

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z = tmp_z.add(goto_programt::make_skip());

  // y: g();
  goto_programt tmp_y;
  goto_programt::targett y;

  do_function_call(lhs, function.false_case(), arguments, tmp_y, mode);

  if(tmp_y.instructions.empty())
    y = tmp_y.add(goto_programt::make_skip());
  else
    y=tmp_y.instructions.begin();

  // v: if(!c) goto y;
  v->complete_goto(y);

  // w: f();
  goto_programt tmp_w;

  do_function_call(lhs, function.true_case(), arguments, tmp_w, mode);

  if(tmp_w.instructions.empty())
    tmp_w.add(goto_programt::make_skip());

  // x: goto z;
  x->complete_goto(z);

  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);
}

void goto_convertt::do_function_call_other(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  // don't know what to do with it
  code_function_callt function_call(lhs, function, arguments);
  function_call.add_source_location()=function.source_location();
  dest.add(goto_programt::make_function_call(
    function_call, function.source_location()));
}
