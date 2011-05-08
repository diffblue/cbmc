/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <arith_tools.h>
#include <std_types.h>

#include <ansi-c/c_types.h>

#include "cpp_typecheck.h"
#include "cpp_util.h"

/*******************************************************************\

Function: cpp_typecheckt::cpp_constructor

  Inputs: non-typchecked object, non-typechecked operands

 Outputs: typechecked code

 Purpose:

\*******************************************************************/

codet cpp_typecheckt::cpp_constructor(
  const locationt &location,
  const exprt &object,
  const exprt::operandst &operands)
{
  exprt object_tc=object;

  typecheck_expr(object_tc);

  typet tmp_type(object_tc.type());
  follow_symbol(tmp_type);

  assert(!is_reference(tmp_type));

  if(tmp_type.id()==ID_array)
  {
    // We allow only one operand and it must be tagged with '#array_ini'.
    // Note that the operand is an array that is used for copy-initialization.
    // In the general case, a program is not allow to use this form of
    // construct. This way of initializing an array is used internaly only.
    // The purpose of the tag #arra_ini is to rule out ill-formed
    // programs.

    if(!operands.empty() && !operands.front().get_bool("#array_ini"))
    {
      err_location(location);
      str << "bad array initializer";
      throw 0;
    }

    assert(operands.empty() || operands.size()==1);

    if(operands.empty() && cpp_is_pod(tmp_type))
    {
      codet nil;
      nil.make_nil();
      return nil;
    }

    const exprt &size_expr=
      to_array_type(tmp_type).size();

    if(size_expr.id()=="infinity")
    {
      // don't initialize
      codet nil;
      nil.make_nil();
      return nil;
    }

    mp_integer s;
    if(to_integer(size_expr, s))
    {
      err_location(tmp_type);
      str << "array size `" << to_string(size_expr)
          << "' is not a constant";
      throw 0;
    }

    /*if(cpp_is_pod(tmp_type))
    {
      code_expressiont new_code;
      exprt op_tc = operands.front();
      typecheck_expr(op_tc);
       // Override constantness
      object_tc.type().set("#constant", false);
      object_tc.set("#lvalue", true);
      side_effect_exprt assign("assign");
      assign.location()=location;
      assign.copy_to_operands(object_tc, op_tc);
      typecheck_side_effect_assignment(assign);
      new_code.expression()=assign;
      return new_code;
    }
    else*/
    {
      codet new_code(ID_block);

      // for each element of the array, call the default constructor
      for(mp_integer i = 0; i < s; ++i)
      {
        exprt::operandst tmp_operands;

        exprt constant=from_integer(i, int_type());
        constant.location()=location;

        exprt index(ID_index);
        index.copy_to_operands(object);
        index.copy_to_operands(constant);
        index.location()=location;

        if(!operands.empty())
        {
          exprt operand(ID_index);
          operand.copy_to_operands(operands.front());
          operand.copy_to_operands(constant);
          operand.location()=location;
          tmp_operands.push_back(operand);
        }

        exprt i_code =
          cpp_constructor(location, index, tmp_operands);

        if(i_code.is_nil())
        {
          new_code.is_nil();
          break;
        }

        new_code.move_to_operands(i_code);
      }
      return new_code;
    }
  }
  else if(cpp_is_pod(tmp_type))
  {
    code_expressiont new_code;
    exprt::operandst operands_tc=operands;

    for(exprt::operandst::iterator
      it=operands_tc.begin();
      it!=operands_tc.end();
      it++)
    {
      typecheck_expr(*it);
      add_implicit_dereference(*it);
    }

    if(operands_tc.size()==0)
    {
      // a POD is NOT initialized
      new_code.make_nil();
    }
    else if(operands_tc.size()==1)
    {
      // Override constantness
      object_tc.type().set(ID_C_constant, false);
      object_tc.set(ID_C_lvalue, true);
      side_effect_exprt assign(ID_assign);
      assign.location()=location;
      assign.copy_to_operands(object_tc, operands_tc.front());
      typecheck_side_effect_assignment(assign);
      new_code.expression()=assign;
    }
    else
    {
      err_location(location);
      str << "initialization of POD requires one argument, "
             "but got " << operands.size() << std::endl;
      throw 0;
    }
    
    return new_code;
  }
  else if(tmp_type.id()==ID_union)
  {
    assert(0); // Todo: union
  }
  else if(tmp_type.id()==ID_struct)
  {
    exprt::operandst operands_tc=operands;

    for(exprt::operandst::iterator
      it=operands_tc.begin();
      it!=operands_tc.end();
      it++)
    {
      typecheck_expr(*it);
      add_implicit_dereference(*it);
    }

    const struct_typet &struct_type=
      to_struct_type(tmp_type);

    // set most-derived bits
    codet block(ID_block);
    for(unsigned i=0; i < struct_type.components().size(); i++)
    {
      const irept &component = struct_type.components()[i];
      if(component.get(ID_base_name) != "@most_derived")
        continue;

      exprt member(ID_member, bool_typet());
      member.set(ID_component_name, component.get(ID_name));
      member.copy_to_operands(object_tc);
      member.location() = location;
      member.set(ID_C_lvalue, object_tc.get_bool(ID_C_lvalue));

      exprt val;
      val.make_false();

      if(!component.get_bool("from_base"))
        val.make_true();

      side_effect_exprt assign(ID_assign);
      assign.location()=location;
      assign.move_to_operands(member,val);
      typecheck_side_effect_assignment(assign);
      code_expressiont code_exp;
      code_exp.expression()=assign;
      block.move_to_operands(code_exp);
    }

    // enter struct scope
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_type.get(ID_name));

    // find name of constructor
    const struct_typet::componentst &components=
      struct_type.components();

    irep_idt constructor_name;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &type=it->type();

      if(!it->get_bool(ID_from_base) &&
         type.id()==ID_code &&
         type.find(ID_return_type).id()==ID_constructor)
      {
        constructor_name=it->get(ID_base_name);
        break;
      }
    }

    // there is always a constructor for non-PODs
    assert(constructor_name!="");

    irept cpp_name(ID_cpp_name);
    cpp_name.get_sub().push_back(irept(ID_name));
    cpp_name.get_sub().back().set(ID_identifier, constructor_name);
    cpp_name.get_sub().back().set(ID_C_location, location);

    side_effect_expr_function_callt function_call;
    function_call.location()=location;
    function_call.function().swap(static_cast<exprt&>(cpp_name));
    function_call.arguments().reserve(operands_tc.size());

    for(exprt::operandst::iterator
        it=operands_tc.begin();
        it!=operands_tc.end();
        it++)
      function_call.op1().copy_to_operands(*it);

    typecheck_side_effect_function_call(function_call);
    assert(function_call.get(ID_statement) == ID_temporary_object);

    exprt &initializer =
      static_cast<exprt &>(function_call.add(ID_initializer));

    assert(initializer.id()==ID_code
           && initializer.get(ID_statement)==ID_expression);

    side_effect_expr_function_callt& func_ini =
      to_side_effect_expr_function_call(initializer.op0());

    exprt& tmp_this = func_ini.arguments().front();
    assert(tmp_this.id() == ID_address_of
           && tmp_this.op0().id() == "new_object");

    exprt address_of(ID_address_of, typet(ID_pointer));
    address_of.type().subtype() = object_tc.type();
    address_of.copy_to_operands(object_tc);
    tmp_this.swap(address_of);

    if(block.operands().empty())
      return to_code(initializer);
    else
    {
      block.move_to_operands(initializer);
      return block;
    }
  }
  else
    assert(false);

  codet nil;
  nil.make_nil();
  return nil;
}

/*******************************************************************\

Function: cpp_typecheckt::new_temporary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::new_temporary(
  const locationt &location,
  const typet &type,
  const exprt::operandst &ops,
  exprt &temporary)
{
  // create temporary object
  exprt tmp_object_expr=exprt(ID_sideeffect, type);
  tmp_object_expr.set(ID_statement, ID_temporary_object);
  tmp_object_expr.location()= location;

  exprt new_object(ID_new_object);
  new_object.location() = tmp_object_expr.location();
  new_object.set(ID_C_lvalue, true);
  new_object.type() = tmp_object_expr.type();

  already_typechecked(new_object);

  codet new_code =
    cpp_constructor(location, new_object, ops);

  if(new_code.is_not_nil())
  {
    if(new_code.get(ID_statement)==ID_assign)
      tmp_object_expr.move_to_operands(new_code.op1());
    else
      tmp_object_expr.add(ID_initializer)=new_code;
  }

  temporary.swap(tmp_object_expr);
}

/*******************************************************************\

Function: cpp_typecheckt::new_temporary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::new_temporary(
  const locationt &location,
  const typet &type,
  const exprt &op,
  exprt &temporary)
{
  exprt::operandst ops;
  ops.push_back(op);
  new_temporary(location,type,ops,temporary);
}
