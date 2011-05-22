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

#include <ansi-c/c_types.h>

#include "goto_convert_class.h"
#include "dynamic_memory.h"

/*******************************************************************\

Function: get_alloc_type_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void get_alloc_type_rec(
  const exprt &src,
  typet &type,
  exprt &size)
{
  const irept &sizeof_type=src.find("#c_sizeof_type");

  if(!sizeof_type.is_nil())
  {
    type=static_cast<const typet &>(sizeof_type);
  }
  else if(src.id()==ID_mult)
  {
    forall_operands(it, src)
      get_alloc_type_rec(*it, type, size);
  }
  else
  {
    size.copy_to_operands(src);
  }
}

/*******************************************************************\

Function: get_alloc_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
static void get_alloc_type(
  const exprt &src,
  typet &type,
  exprt &size)
{
  type.make_nil();
  size.make_nil();

  get_alloc_type_rec(src, type, size);

  if(type.is_nil())
    type=char_type();

  if(size.has_operands())
  {
    if(size.operands().size()==1)
    {
      exprt tmp;
      tmp.swap(size.op0());
      size.swap(tmp);
    }
    else
    {
      size.id(ID_mult);
      size.type()=size.op0().type();
    }
    
    if(size.type()!=size_type())
      size.make_typecast(size_type());
  }
}
#endif

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

  exprt rhs=exprt(ID_sideeffect, lhs.type());
  rhs.set(ID_statement, "prob_uniform");
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

  exprt rhs=exprt(ID_sideeffect, lhs.type());
  rhs.set(ID_statement, "prob_coin");
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
    exprt printf_code(ID_sideeffect,
      static_cast<const typet &>(function.type().find(ID_return_type)));

    printf_code.set(ID_statement, ID_printf);

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
  
  bool is_assume=identifier==CPROVER_PREFIX "assume" ||
                 identifier=="specc::__CPROVER_assume";

  bool is_assert=identifier=="c::assert" ||
                 identifier=="specc::assert";

  bool is_predicate=identifier==CPROVER_PREFIX "predicate" ||
                 identifier=="specc::__CPROVER_predicate";

  if(is_assume || is_assert || is_predicate)
  {
    if(arguments.size()!=1)
    {
      err_location(function);
      throw "`"+id2string(identifier)+"' expected to have one argument";
    }

    if(is_predicate) {
    	goto_programt::targett t = dest.add_instruction(OTHER);
    	t->guard = arguments.front();
    	t->location = function.location();
    	t->location.set("user-provided", true);
    	t->code = ID_user_specified_predicate;
		t->code.set_statement(ID_user_specified_predicate);
	  return;

    }

    if(is_assume && !options.get_bool_option("assumptions"))
      return;

    if(is_assert && !options.get_bool_option("assertions"))
      return;

    goto_programt::targett t=dest.add_instruction(
      is_assume?ASSUME:ASSERT);
    t->guard=arguments.front();
    t->location=function.location();
    t->location.set("user-provided", true);

    if(is_assert)
      t->location.set(ID_property, ID_assertion);
    
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
    t->location.set(ID_property, ID_assertion);
    t->location.set(ID_comment, description);
    
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
  else if(identifier==CPROVER_PREFIX "input")
  {
    do_input(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "cover")
  {
    do_cover(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "output")
  {
    do_output(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_begin")
  {
    do_atomic_begin(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "atomic_end")
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
          has_prefix(id2string(identifier), "cpp::nondet_"))
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
  else if(identifier==CPROVER_PREFIX "array_equal")
  {
    do_array_equal(lhs, function, arguments, dest);
  }
  else if(identifier==CPROVER_PREFIX "array_copy")
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
    t->location.set(ID_property, ID_assertion);
    t->location.set(ID_comment, description);
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
    t->location.set(ID_property, ID_assertion);
    t->location.set(ID_comment, description);
    // we ignore any LHS
  }
  else if(identifier=="c::_wassert")
  {
    // this is Windows

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
    t->location.set(ID_property, ID_assertion);
    t->location.set(ID_comment, description);
    // we ignore any LHS
  }
  else if(identifier=="c::__builtin_prefetch")
  {
    // does nothing
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
