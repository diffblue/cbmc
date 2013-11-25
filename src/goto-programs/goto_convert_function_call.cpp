/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/replace_expr.h>
#include <util/expr_util.h>
#include <util/location.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/std_expr.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::convert_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_function_call(
  const code_function_callt &function_call,
  goto_programt &dest)
{
  do_function_call(
    function_call.lhs(),
    function_call.function(),
    function_call.arguments(),
    dest);
}

/*******************************************************************\

Function: goto_convertt::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_function_call(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  // make it all side effect free
  
  exprt new_lhs=lhs,
        new_function=function;
  
  exprt::operandst new_arguments=arguments;

  if(!new_lhs.is_nil())
    clean_expr(new_lhs, dest);

  clean_expr(new_function, dest);
  
  // the arguments of __noop do not get evaluated
  if(new_function.id()==ID_symbol &&
     to_symbol_expr(new_function).get_identifier()=="c::__noop")
  {
    new_arguments.clear();
  }

  Forall_expr(it, new_arguments)
    clean_expr(*it, dest);

  // split on the function

  if(new_function.id()==ID_dereference)
  {
    do_function_call_dereference(new_lhs, new_function, new_arguments, dest);
  }
  else if(new_function.id()==ID_if)
  {
    do_function_call_if(new_lhs, new_function, new_arguments, dest);
  }
  else if(new_function.id()==ID_symbol)
  {
    do_function_call_symbol(new_lhs, new_function, new_arguments, dest);
  }
  else if(new_function.id()=="NULL-object")
  {
  }
  else
  {
    err_location(function);
    throw "unexpected function argument: "+new_function.id_string();
  }
}

/*******************************************************************\

Function: goto_convertt::do_function_call_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_function_call_if(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(function.operands().size()!=3)
  {
    err_location(function);
    throw "if expects three operands";
  }
  
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
  goto_programt::targett v=tmp_v.add_instruction();

  // do the x label
  goto_programt tmp_x;
  goto_programt::targett x=tmp_x.add_instruction();

  // do the z label
  goto_programt tmp_z;
  goto_programt::targett z=tmp_z.add_instruction();
  z->make_skip();

  // y: g();
  goto_programt tmp_y;
  goto_programt::targett y;

  do_function_call(lhs, function.op2(), arguments, tmp_y);

  if(tmp_y.instructions.empty())
    y=tmp_y.add_instruction(SKIP);
  else
    y=tmp_y.instructions.begin();

  // v: if(!c) goto y;
  v->make_goto(y);
  v->guard=function.op0();
  v->guard.make_not();
  v->location=function.op0().location();

  // w: f();
  goto_programt tmp_w;

  do_function_call(lhs, function.op1(), arguments, tmp_w);

  if(tmp_w.instructions.empty())
    tmp_w.add_instruction(SKIP);

  // x: goto z;
  x->make_goto(z);

  dest.destructive_append(tmp_v);
  dest.destructive_append(tmp_w);
  dest.destructive_append(tmp_x);
  dest.destructive_append(tmp_y);
  dest.destructive_append(tmp_z);
}

/*******************************************************************\

Function: goto_convertt::do_function_call_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_function_call_dereference(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  // don't know what to do with it
  goto_programt::targett t=dest.add_instruction(FUNCTION_CALL);

  code_function_callt function_call;
  function_call.location()=function.location();
  function_call.lhs()=lhs;
  function_call.function()=function;
  function_call.arguments()=arguments;
  
  t->location=function.location();
  t->code.swap(function_call);
}
