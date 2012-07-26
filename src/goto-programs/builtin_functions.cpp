/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <replace_expr.h>
#include <expr_util.h>
#include <rational_tools.h>
#include <location.h>
#include <cprover_prefix.h>
#include <prefix.h>
#include <arith_tools.h>
#include <simplify_expr.h>
#include <std_code.h>
#include <std_expr.h>
#include <symbol.h>

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"
#include "dynamic_memory.h"

/*******************************************************************\

Function: goto_convertt::do_prob_uniform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_prob_uniform(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier=function.get(ID_identifier);

  // make it a side effect if there is an LHS
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have two arguments";
  }

  if(lhs.is_nil())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have LHS";
  }

  exprt rhs=sideeffect_exprt("prob_uniform", lhs.type());
  rhs.location()=function.location();

  if(lhs.type().id()!=ID_unsignedbv &&
     lhs.type().id()!=ID_signedbv)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected other type";
  }

  if(arguments[0].type().id()!=lhs.type().id() ||
     arguments[1].type().id()!=lhs.type().id())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected operands to be of same type as LHS";
  }

  if(!arguments[0].is_constant() ||
     !arguments[1].is_constant())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected operands to be constant literals";
  }

  mp_integer lb, ub;

  if(to_integer(arguments[0], lb) ||
     to_integer(arguments[1], ub))
  {
    err_location(function);
    throw "error converting operands";
  }

  if(lb > ub)
  {
    err_location(function);
    throw "expected lower bound to be smaller or equal to the upper bound";
  }

  rhs.copy_to_operands(arguments[0], arguments[1]);

  code_assignt assignment(lhs, rhs);
  assignment.location()=function.location();
  copy(assignment, ASSIGN, dest);
}

/*******************************************************************\

Function: goto_convertt::do_prob_coin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_prob_coin(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &identifier=function.get(ID_identifier);

  // make it a side effect if there is an LHS
  if(arguments.size()!=2) 
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have two arguments";
  }
  
  if(lhs.is_nil())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected to have LHS";
  }

  exprt rhs=sideeffect_exprt("prob_coin", lhs.type());
  rhs.location()=function.location();

  if(lhs.type()!=bool_typet())
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected bool";
  }

  if(arguments[0].type().id()!=ID_unsignedbv ||
     arguments[0].id()!=ID_constant)
  {
    err_location(function);
    throw "`"+id2string(identifier)+"' expected first "
          "operand to be a constant literal of type unsigned long";
  }

  mp_integer num, den;

  if(to_integer(arguments[0], num) ||
     to_integer(arguments[1], den))
  {
    err_location(function);
    throw "error converting operands";
  }

  if(num-den > mp_integer(0))
  {
    err_location(function);
    throw "probability has to be smaller than 1";
  }

  if(den == mp_integer(0))
  {
    err_location(function);
    throw "denominator may not be zero";
  }

  rationalt numerator(num), denominator(den);
  rationalt prob = numerator / denominator;

  rhs.copy_to_operands(from_rational(prob));

  code_assignt assignment(lhs, rhs);
  assignment.location()=function.location();
  copy(assignment, ASSIGN, dest);
}

/*******************************************************************\

Function: goto_convertt::do_printf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_printf(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  const irep_idt &f_id=function.get(ID_identifier);

  if(f_id==CPROVER_PREFIX "printf" ||
     f_id=="c::printf")
  {
    typet return_type=static_cast<const typet &>(function.type().find(ID_return_type));
    sideeffect_exprt printf_code(ID_printf, return_type);

    printf_code.operands()=arguments;
    printf_code.location()=function.location();

    if(lhs.is_not_nil())
    {
      code_assignt assignment(lhs, printf_code);
      assignment.location()=function.location();
      copy(assignment, ASSIGN, dest);
    }
    else
    {
      printf_code.id(ID_code);
      printf_code.type()=typet(ID_code);
      copy(to_code(printf_code), OTHER, dest);
    }
  }
}

/*******************************************************************\

Function: goto_convertt::do_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_input(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet input_code;
  input_code.set_statement(ID_input);
  input_code.operands()=arguments;
  input_code.location()=function.location();
  
  if(arguments.size()<2)
  {
    err_location(function);
    throw "input takes at least two arguments";
  }
    
  copy(input_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_cover(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet output_code;
  output_code.set_statement(ID_output);
  output_code.location()=function.location();

  if(arguments.size()!=1)
  {
    err_location(function);
    throw "cover takes one argument";
  }
  
  // build string constant
  exprt string_constant(ID_string_constant);
  string_constant.type()=array_typet();
  string_constant.type().subtype()=char_type();
  string_constant.set(ID_value, ID_cover);
  
  index_exprt index_expr;
  index_expr.type()=char_type();
  index_expr.array()=string_constant;
  index_expr.index()=gen_zero(index_type());
  
  output_code.copy_to_operands(address_of_exprt(index_expr));
  
  forall_expr(it, arguments)
    output_code.copy_to_operands(*it);
    
  copy(output_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_output(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  codet output_code;
  output_code.set_statement(ID_output);
  output_code.operands()=arguments;
  output_code.location()=function.location();
  
  if(arguments.size()<2)
  {
    err_location(function);
    throw "output takes at least two arguments";
  }
    
  copy(output_code, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_atomic_begin

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_atomic_begin(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    err_location(lhs);
    throw "atomic_begin does not expect an LHS";
  }

  if(!arguments.empty())
  {
    err_location(function);
    throw "atomic_begin takes no arguments";
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_BEGIN);
  t->location=function.location();
}

/*******************************************************************\

Function: goto_convertt::do_atomic_end

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_atomic_end(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(lhs.is_not_nil())
  {
    err_location(lhs);
    throw "atomic_end does not expect an LHS";
  }

  if(!arguments.empty())
  {
    err_location(function);
    throw "atomic_end takes no arguments";
  }

  goto_programt::targett t=dest.add_instruction(ATOMIC_END);
  t->location=function.location();
}

/*******************************************************************\

Function: goto_convertt::do_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_cpp_new(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  if(lhs.is_nil())
    throw "do_cpp_new without lhs is yet to be implemented";
  
  // build size expression
  exprt object_size=
    static_cast<const exprt &>(rhs.find(ID_sizeof));

  bool new_array=rhs.get(ID_statement)==ID_cpp_new_array;
  
  exprt count;

  if(new_array)
  {
    count=static_cast<const exprt &>(rhs.find(ID_size));

    if(count.type()!=object_size.type())
      count.make_typecast(object_size.type());

    // might have side-effect
    clean_expr(count, dest);
  }

  exprt tmp_symbol_expr;

  // is this a placement new?
  if(rhs.operands().size()==0) // no, "regular" one
  {
    // call __new or __new_array
    exprt new_symbol=symbol_expr(
      ns.lookup(new_array?"c::__new_array":"c::__new"));
    
    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=
      code_type.return_type();

    assert(code_type.arguments().size()==1 ||
           code_type.arguments().size()==2);

    const symbolt &tmp_symbol=
      new_tmp_symbol(return_type, "new", dest, rhs.location());
    
    tmp_symbol_expr=symbol_expr(tmp_symbol);
    
    code_function_callt new_call;
    new_call.function()=new_symbol;
    if(new_array) new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.set("#type", lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.location()=rhs.location();
    
    convert(new_call, dest);
  }
  else if(rhs.operands().size()==1)
  {
    // call __placement_new
    exprt new_symbol=symbol_expr(
      ns.lookup(new_array?"c::__placement_new_array":"c::__placement_new"));
    
    const code_typet &code_type=
      to_code_type(new_symbol.type());

    const typet &return_type=code_type.return_type();
    
    assert(code_type.arguments().size()==2 ||
           code_type.arguments().size()==3);

    const symbolt &tmp_symbol=
      new_tmp_symbol(return_type, "new", dest, rhs.location());

    tmp_symbol_expr=symbol_expr(tmp_symbol);

    code_function_callt new_call;
    new_call.function()=new_symbol;
    if(new_array) new_call.arguments().push_back(count);
    new_call.arguments().push_back(object_size);
    new_call.arguments().push_back(rhs.op0()); // memory location
    new_call.set("#type", lhs.type().subtype());
    new_call.lhs()=tmp_symbol_expr;
    new_call.location()=rhs.location();

    for(unsigned i=0; i<code_type.arguments().size(); i++)
      if(new_call.arguments()[i].type()!=code_type.arguments()[i].type())
        new_call.arguments()[i].make_typecast(code_type.arguments()[i].type());
    
    convert(new_call, dest);
  }
  else
    throw "cpp_new expected to have 0 or 1 operands";

  goto_programt::targett t_n=dest.add_instruction(ASSIGN);
  t_n->code=code_assignt(
    lhs, typecast_exprt(tmp_symbol_expr, lhs.type()));
  t_n->location=rhs.find_location();
    
  // grab initializer
  goto_programt tmp_initializer;
  cpp_new_initializer(lhs, rhs, tmp_initializer);

  dest.destructive_append(tmp_initializer);
}

/*******************************************************************\

Function: goto_convertt::cpp_new_initializer

  Inputs:

 Outputs:

 Purpose: builds a goto program for object initialization
          after new

\*******************************************************************/

void goto_convertt::cpp_new_initializer(
  const exprt &lhs,
  const side_effect_exprt &rhs,
  goto_programt &dest)
{
  exprt initializer=
    static_cast<const exprt &>(rhs.find(ID_initializer));

  if(initializer.is_not_nil())
  {
    if(rhs.get_statement()=="cpp_new[]")
    {
      // build loop
    }
    else if(rhs.get_statement()==ID_cpp_new)
    {
      // just one object
      exprt deref_lhs(ID_dereference, rhs.type().subtype());
      deref_lhs.copy_to_operands(lhs);
      
      replace_new_object(deref_lhs, initializer);
      convert(to_code(initializer), dest);
    }
    else
      assert(false);
  }
}

/*******************************************************************\

Function: goto_convertt::get_array_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt goto_convertt::get_array_argument(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    assert(src.operands().size()==1);
    return get_array_argument(src.op0());
  }

  if(src.id()!=ID_address_of)
  {
    err_location(src);
    throw "expected array-pointer as argument";
  }
  
  assert(src.operands().size()==1);

  if(src.op0().id()!=ID_index)
  {
    err_location(src);
    throw "expected array-element as argument";
  }
  
  assert(src.op0().operands().size()==2);

  if(ns.follow(src.op0().op0().type()).id()!=ID_array)
  {
    err_location(src);
    throw "expected array as argument";
  }

  return src.op0().op0();
}

/*******************************************************************\

Function: goto_convertt::do_array_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_set(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_set expects two arguments";
  }

  codet array_set_statement;
  array_set_statement.set_statement(ID_array_set);
  array_set_statement.operands()=arguments;

  copy(array_set_statement, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_array_copy

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_copy(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_copy expects two arguments";
  }

  codet array_set_statement;
  array_set_statement.set_statement(ID_array_copy);
  array_set_statement.operands()=arguments;

  copy(array_set_statement, OTHER, dest);
}

/*******************************************************************\

Function: goto_convertt::do_array_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::do_array_equal(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(arguments.size()!=2)
  {
    err_location(function);
    throw "array_equal expects two arguments";
  }
  
  const typet &arg0_type=ns.follow(arguments[0].type());
  const typet &arg1_type=ns.follow(arguments[1].type());
  
  if(arg0_type.id()!=ID_pointer ||
     arg1_type.id()!=ID_pointer)
  {
    err_location(function);
    throw "array_equal expects pointer arguments";
  }
  
  if(lhs.is_not_nil())
  {
    code_assignt assignment;
    
    // add dereferencing here
    dereference_exprt lhs_array, rhs_array;
    lhs_array.op0()=arguments[0];
    rhs_array.op0()=arguments[1];
    lhs_array.type()=arg0_type.subtype();
    rhs_array.type()=arg1_type.subtype();
    
    assignment.lhs()=lhs;
    assignment.rhs()=binary_exprt(
      lhs_array, ID_array_equal, rhs_array, lhs.type());
    
    convert(assignment, dest);
  }
}

/*******************************************************************\

Function: goto_convertt::do_function_call_symbol

  Inputs:

 Outputs:

 Purpose: add function calls to function queue for later
          processing

\*******************************************************************/

void goto_convertt::do_function_call_symbol(
  const exprt &lhs,
  const exprt &function,
  const exprt::operandst &arguments,
  goto_programt &dest)
{
  if(function.get_bool("#invalid_object"))
    return; // ignore

  // lookup symbol
  const irep_idt &identifier=function.get(ID_identifier);

  const symbolt *symbol;
  if(ns.lookup(identifier, symbol))
  {
    err_location(function);
    throw "error: function `"+id2string(identifier)+"' not found";
  }

  if(symbol->type.id()!=ID_code)
  {
    err_location(function);
    throw "error: function `"+id2string(identifier)+"' type mismatch: expected code";
  }
  
  if(identifier==CPROVER_PREFIX "parameter_predicates" || 
     identifier==CPROVER_PREFIX "return_predicates")
  {
    if(arguments.size() != 0)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have no arguments";
    }

    goto_programt::targett t = dest.add_instruction(OTHER);
    t->location = function.location();
    t->location.set("user-provided", true);
    if(identifier==CPROVER_PREFIX "parameter_predicates")
    {
      t->code = codet(ID_user_specified_parameter_predicates);
      t->code.set_statement(ID_user_specified_parameter_predicates);
    }
    else
    {
      t->code = codet(ID_user_specified_return_predicates);
      t->code.set_statement(ID_user_specified_return_predicates);
    }
  }
  else if(identifier==CPROVER_PREFIX "predicate")
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->guard=arguments.front();
    t->location=function.location();
    t->location.set("user-provided", true);
    t->code=codet(ID_user_specified_predicate);
  }
  else if(identifier==CPROVER_PREFIX "assume" ||
          identifier=="c::__VERIFIER_assume")
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    if(!options.get_bool_option("assumptions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSUME);
    t->guard=arguments.front();
    t->location=function.location();
    t->location.set("user-provided", true);
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier=="c::assert")
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    if(!options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments.front();
    t->location=function.location();
    t->location.set("user-provided", true);
    t->location.set_property(ID_assertion);
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier==CPROVER_PREFIX "assert")
  {
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    const irep_idt description=
      get_string_constant(arguments[1]);

    if(!options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=arguments[0];
    t->location=function.location();
    t->location.set("user-provided", true);
    t->location.set_property(ID_assertion);
    t->location.set_comment(description);
    
    // let's double-check the type of the argument
    if(t->guard.type().id()!=ID_bool)
      t->guard.make_typecast(bool_typet());

    if(lhs.is_not_nil())
    {
      err_location(function);
      throw id2string(identifier)+" expected not to have LHS";
    }
  }
  else if(identifier==CPROVER_PREFIX "printf")
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "input" ||
          identifier=="c::__CPROVER::input")
  {
    do_input(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "cover" ||
          identifier=="c::__CPROVER::cover")
  {
    do_cover(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "output" ||
          identifier=="c::__CPROVER::output")
  {
    do_output(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_begin" ||
          identifier=="c::__CPROVER::atomic_begin")
  {
    do_atomic_begin(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_end" ||
          identifier=="c::__CPROVER::atomic_end")
  {
    do_atomic_end(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "prob_biased_coin")
  {
    do_prob_coin(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "prob_uniform_"))
  {
    do_prob_uniform(lhs, function, arguments, dest);
  }
  else if(has_prefix(id2string(identifier), "c::nondet_") ||
          has_prefix(id2string(identifier), "c::__VERIFIER_nondet_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil()) return;

    exprt rhs=side_effect_expr_nondett(lhs.type());
    rhs.location()=function.location();

    code_assignt assignment(lhs, rhs);
    assignment.location()=function.location();
    copy(assignment, ASSIGN, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "uninterpreted_"))
  {
    // make it a side effect if there is an LHS
    if(lhs.is_nil()) return;

    function_application_exprt rhs;
    rhs.type()=lhs.type();
    rhs.location()=function.location();
    rhs.function()=function;
    rhs.arguments()=arguments;

    code_assignt assignment(lhs, rhs);
    assignment.location()=function.location();
    copy(assignment, ASSIGN, dest);
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "array_set"))
  {
    do_array_set(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_equal" ||
          identifier=="c::__CPROVER::array_equal")
  {
    do_array_equal(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_copy" ||
          identifier=="c::__CPROVER::array_equal")
  {
    do_array_copy(lhs, function, arguments, dest);
  }
  else if(identifier=="c::printf" ||
          identifier=="c::fprintf" ||
          identifier=="c::sprintf" ||
          identifier=="c::snprintf")
  {
    do_printf(lhs, function, arguments, dest);
  }
  else if(identifier=="c::__assert_fail")
  {
    // __assert_fail is Linux
    // These take four arguments:
    // "expression", "file.c", line, __func__

    if(arguments.size()!=4)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }
    
    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    if(!options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->location=function.location();
    t->location.set("user-provided", true);
    t->location.set_property(ID_assertion);
    t->location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="c::__assert_rtn")
  {
    // __assert_rtn has been seen on MacOS    
    // It takes four arguments:
    // __func__, "file.c", line, "expression"

    if(arguments.size()!=4)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have four arguments";
    }
    
    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[3]));

    if(!options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->location=function.location();
    t->location.set("user-provided", true);
    t->location.set_property(ID_assertion);
    t->location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier=="c::_wassert")
  {
    // This is Windows. The arguments are
    // L"expression", L"file.c", line

    if(arguments.size()!=3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have three arguments";
    }

    const irep_idt description=
      "assertion "+id2string(get_string_constant(arguments[0]));

    if(!options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(ASSERT);
    t->guard=false_exprt();
    t->location=function.location();
    t->location.set("user-provided", true);
    t->location.set_property(ID_assertion);
    t->location.set_comment(description);
    // we ignore any LHS
  }
  else if(identifier==CPROVER_PREFIX "fence")
  {
    if(arguments.size()<1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least one argument";
    }

    goto_programt::targett t=dest.add_instruction(OTHER);
    t->location=function.location();
    t->code.set(ID_statement, ID_fence);

    forall_expr(it, arguments)
    {
      const irep_idt kind=get_string_constant(*it);
      t->code.set(kind, true);
    }
  }
  else if(identifier=="c::__builtin_prefetch")
  {
    // does nothing
  }
  else if(identifier==ID_gcc_builtin_va_arg)
  {
    // This does two things.
    // 1) Move list pointer to next argument.
    //    Done by gcc_builtin_va_arg_next.
    // 2) Return value of argument.
    //    This is just dereferencing.

    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }
    
    {
      sideeffect_exprt rhs(ID_gcc_builtin_va_arg_next, arguments[0].type());
      rhs.copy_to_operands(arguments[0]);
      goto_programt::targett t1=dest.add_instruction(ASSIGN);
      t1->location=function.location();
      t1->code=code_assignt(arguments[0], rhs);
    }

    if(lhs.is_not_nil())
    {
      typet t=pointer_typet();
      t.subtype()=lhs.type();
      dereference_exprt rhs(lhs.type());
      rhs.op0()=typecast_exprt(arguments[0], t);
      rhs.location()=function.location();
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->location=function.location();
      t2->code=code_assignt(lhs, rhs);
    }
  }
  else if(identifier=="c::__builtin_va_copy")
  {
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    exprt lhs=arguments[0];
    exprt rhs=typecast_exprt(arguments[1], lhs.type());
    
    if(lhs.id()!=ID_symbol)
    {
      err_location(lhs);
      throw "vs_copy argument expected to be symbol";
    }    
    
    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->location=function.location();
    t->code=code_assignt(lhs, rhs);
  }
  else if(identifier=="c::__builtin_va_start")
  {
    // Set the list argument to be the address of the
    // parameter argument.
    if(arguments.size()!=2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have two arguments";
    }
    
    exprt lhs=arguments[0];
    exprt rhs=typecast_exprt(
      address_of_exprt(arguments[1]), lhs.type());

    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->location=function.location();
    t->code=code_assignt(lhs, rhs);
  }
  else if(identifier=="c::__builtin_va_end")
  {
    // Invalidates the argument. We do so by setting it to NULL.
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }
    
    goto_programt::targett t=dest.add_instruction(ASSIGN);
    t->location=function.location();
    t->code=code_assignt(arguments[0], gen_zero(arguments[0].type()));
  }
  else if(identifier=="c::__sync_fetch_and_add" ||
          identifier=="c::__sync_fetch_and_sub" ||
          identifier=="c::__sync_fetch_and_or" ||
          identifier=="c::__sync_fetch_and_and" ||
          identifier=="c::__sync_fetch_and_xor" ||
          identifier=="c::__sync_fetch_and_nand")
  {
    // type __sync_fetch_and_OP(type *ptr, type value, ...)
    // { tmp = *ptr; *ptr OP= value; return tmp; }

    if(arguments.size()<2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least two arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }
    
    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->location=function.location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->location=function.location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    irep_idt op_id=
      identifier=="c::__sync_fetch_and_add"?ID_plus:
      identifier=="c::__sync_fetch_and_sub"?ID_minus:
      identifier=="c::__sync_fetch_and_or"?ID_bitor:
      identifier=="c::__sync_fetch_and_and"?ID_bitand:
      identifier=="c::__sync_fetch_and_xor"?ID_bitxor:
      identifier=="c::__sync_fetch_and_nand"?ID_bitnand:
      ID_nil;
    
    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->location=function.location();
    t3->code=code_assignt(deref_ptr, op_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->location=function.location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);

    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->location=function.location();
  }
  else if(identifier=="c::__sync_add_and_fetch" ||
          identifier=="c::__sync_sub_and_fetch" ||
          identifier=="c::__sync_or_and_fetch" ||
          identifier=="c::__sync_and_and_fetch" ||
          identifier=="c::__sync_xor_and_fetch" ||
          identifier=="c::__sync_nand_and_fetch")
  {
    // type __sync_OP_and_fetch (type *ptr, type value, ...)
    // { *ptr OP= value; return *ptr; }

    if(arguments.size()<2)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least two arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }
    
    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->location=function.location();

    irep_idt op_id=
      identifier=="c::__sync_add_and_fetch"?ID_plus:
      identifier=="c::__sync_sub_and_fetch"?ID_minus:
      identifier=="c::__sync_or_and_fetch"?ID_bitor:
      identifier=="c::__sync_and_and_fetch"?ID_bitand:
      identifier=="c::__sync_xor_and_fetch"?ID_bitxor:
      identifier=="c::__sync_nand_and_fetch"?ID_bitnand:
      ID_nil;
    
    // build *ptr=*ptr OP arguments[1];
    binary_exprt op_expr(deref_ptr, op_id, arguments[1], deref_ptr.type());
    if(op_expr.op1().type()!=op_expr.type())
      op_expr.op1().make_typecast(op_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->location=function.location();
    t3->code=code_assignt(deref_ptr, op_expr);
    
    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->location=function.location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }

    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->location=function.location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->location=function.location();
  }
  else if(identifier=="c::__sync_bool_compare_and_swap")
  {
    // These builtins perform an atomic compare and swap. That is, if the
    // current value of *ptr is oldval, then write newval into *ptr.  The
    // "bool" version returns true if the comparison is successful and
    // newval was written.  The "val" version returns the contents of *ptr
    // before the operation.

    // These are type-polymorphic, which makes it hard to put
    // them into ansi-c/library.

    // bool __sync_bool_compare_and_swap (type *ptr, type oldval, type newval, ...)
    
    if(arguments.size()<3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least three arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->location=function.location();

    // build *ptr==oldval    
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());
      
    if(lhs.is_not_nil())
    {
      // return *ptr==oldval
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->location=function.location();
      t2->code=code_assignt(lhs, equal);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    // build (*ptr==oldval)?newval:*ptr    
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->location=function.location();
    t3->code=code_assignt(deref_ptr, if_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->location=function.location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->location=function.location();
  }
  else if(identifier=="c::__sync_val_compare_and_swap")
  {
    // type __sync_val_compare_and_swap (type *ptr, type oldval, type newval, ...)
    if(arguments.size()<3)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have at least three arguments";
    }

    if(arguments[0].type().id()!=ID_pointer)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have pointer argument";
    }

    // build *ptr
    dereference_exprt deref_ptr(arguments[0], arguments[0].type().subtype());

    goto_programt::targett t1=dest.add_instruction(ATOMIC_BEGIN);
    t1->location=function.location();

    if(lhs.is_not_nil())
    {
      // return *ptr
      goto_programt::targett t2=dest.add_instruction(ASSIGN);
      t2->location=function.location();
      t2->code=code_assignt(lhs, deref_ptr);
      if(t2->code.op0().type()!=t2->code.op1().type())
        t2->code.op1().make_typecast(t2->code.op0().type());
    }
    
    // build *ptr==oldval    
    equal_exprt equal(deref_ptr, arguments[1]);
    if(equal.op1().type()!=equal.op0().type())
      equal.op1().make_typecast(equal.op0().type());
      
    // build (*ptr==oldval)?newval:*ptr    
    if_exprt if_expr(equal, arguments[2], deref_ptr, deref_ptr.type());
    if(if_expr.op1().type()!=if_expr.type())
      if_expr.op1().make_typecast(if_expr.type());

    goto_programt::targett t3=dest.add_instruction(ASSIGN);
    t3->location=function.location();
    t3->code=code_assignt(deref_ptr, if_expr);
    
    // this instruction implies an mfence, i.e., WRfence
    goto_programt::targett t4=dest.add_instruction(OTHER);
    t4->location=function.location();
    t4->code=codet(ID_fence);
    t4->code.set(ID_WRfence, true);
    
    goto_programt::targett t5=dest.add_instruction(ATOMIC_END);
    t5->location=function.location();
  }
  else if(identifier=="c::__sync_lock_test_and_set")
  {
    // type __sync_lock_test_and_set (type *ptr, type value, ...)
    
    // This builtin, as described by Intel, is not a traditional
    // test-and-set operation, but rather an atomic exchange operation. 
    // It writes value into *ptr, and returns the previous contents of
    // *ptr.  Many targets have only minimal support for such locks, and
    // do not support a full exchange operation.  In this case, a target
    // may support reduced functionality here by which the only valid
    // value to store is the immediate constant 1.  The exact value
    // actually stored in *ptr is implementation defined.
  }
  else if(identifier=="c::__sync_lock_release")
  {
    // This builtin is not a full barrier, but rather an acquire barrier.
    // This means that references after the builtin cannot move to (or be
    // speculated to) before the builtin, but previous memory stores may
    // not be globally visible yet, and previous memory loads may not yet
    // be satisfied.

    // void __sync_lock_release (type *ptr, ...)
  }
  else
  {
    do_function_call_symbol(*symbol);

    // insert function call
    code_function_callt function_call;
    function_call.lhs()=lhs;
    function_call.function()=function;
    function_call.arguments()=arguments;
    function_call.location()=function.location();

    copy(function_call, FUNCTION_CALL, dest);
  }
}
