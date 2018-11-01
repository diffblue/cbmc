/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/arith_tools.h>
#include <util/std_types.h>

#include <util/c_types.h>

#include "cpp_util.h"

/// \param source_location: source location for generated code
/// \param object: non-typechecked object
/// \param operands: non-typechecked operands
/// \return typechecked code
optionalt<codet> cpp_typecheckt::cpp_constructor(
  const source_locationt &source_location,
  const exprt &object,
  const exprt::operandst &operands)
{
  exprt object_tc=object;

  typecheck_expr(object_tc);

  elaborate_class_template(object_tc.type());

  typet tmp_type(follow(object_tc.type()));

  assert(!is_reference(tmp_type));

  if(tmp_type.id()==ID_array)
  {
    // We allow only one operand and it must be tagged with '#array_ini'.
    // Note that the operand is an array that is used for copy-initialization.
    // In the general case, a program is not allowed to use this form of
    // construct. This way of initializing an array is used internally only.
    // The purpose of the tag #array_ini is to rule out ill-formed
    // programs.

    if(!operands.empty() && !operands.front().get_bool(ID_C_array_ini))
    {
      error().source_location=source_location;
      error() << "bad array initializer" << eom;
      throw 0;
    }

    assert(operands.empty() || operands.size()==1);

    if(operands.empty() && cpp_is_pod(tmp_type))
      return {};

    const exprt &size_expr=
      to_array_type(tmp_type).size();

    if(size_expr.id() == ID_infinity)
      return {}; // don't initialize

    exprt tmp_size=size_expr;
    make_constant_index(tmp_size);

    mp_integer s;
    if(to_integer(tmp_size, s))
    {
      error().source_location=source_location;
      error() << "array size `" << to_string(size_expr)
              << "' is not a constant" << eom;
      throw 0;
    }

    /*if(cpp_is_pod(tmp_type))
    {
      code_expressiont new_code;
      exprt op_tc=operands.front();
      typecheck_expr(op_tc);
       // Override constantness
      object_tc.type().set("ID_C_constant", false);
      object_tc.set("ID_C_lvalue", true);
      side_effect_exprt assign(ID_assign);
      assign.add_source_location()=source_location;
      assign.copy_to_operands(object_tc, op_tc);
      typecheck_side_effect_assignment(assign);
      new_code.expression()=assign;
      return new_code;
    }
    else*/
    {
      code_blockt new_code;

      // for each element of the array, call the default constructor
      for(mp_integer i=0; i < s; ++i)
      {
        exprt::operandst tmp_operands;

        exprt constant=from_integer(i, index_type());
        constant.add_source_location()=source_location;

        index_exprt index(object, constant);
        index.add_source_location()=source_location;

        if(!operands.empty())
        {
          index_exprt operand(operands.front(), constant);
          operand.add_source_location()=source_location;
          tmp_operands.push_back(operand);
        }

        auto i_code = cpp_constructor(source_location, index, tmp_operands);

        if(i_code.has_value())
          new_code.add(std::move(i_code.value()));
      }
      return std::move(new_code);
    }
  }
  else if(cpp_is_pod(tmp_type))
  {
    exprt::operandst operands_tc=operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    if(operands_tc.empty())
    {
      // a POD is NOT initialized
      return {};
    }
    else if(operands_tc.size()==1)
    {
      // Override constantness
      object_tc.type().set(ID_C_constant, false);
      object_tc.set(ID_C_lvalue, true);
      side_effect_exprt assign(ID_assign, typet(), source_location);
      assign.copy_to_operands(object_tc, operands_tc.front());
      typecheck_side_effect_assignment(assign);
      code_expressiont new_code;
      new_code.expression()=assign;
      return std::move(new_code);
    }
    else
    {
      error().source_location=source_location;
      error() << "initialization of POD requires one argument, "
                 "but got " << operands.size() << eom;
      throw 0;
    }
  }
  else if(tmp_type.id()==ID_union)
  {
    UNREACHABLE; // Todo: union
  }
  else if(tmp_type.id()==ID_struct)
  {
    exprt::operandst operands_tc=operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    const struct_typet &struct_type=
      to_struct_type(tmp_type);

    // set most-derived bits
    code_blockt block;
    for(const auto &component : struct_type.components())
    {
      if(component.get_base_name() != "@most_derived")
        continue;

      member_exprt member(object_tc, component.get_name(), bool_typet());
      member.add_source_location()=source_location;
      member.set(ID_C_lvalue, object_tc.get_bool(ID_C_lvalue));

      exprt val=false_exprt();

      if(!component.get_bool(ID_from_base))
        val=true_exprt();

      side_effect_exprt assign(ID_assign, typet(), source_location);
      assign.move_to_operands(member, val);
      typecheck_side_effect_assignment(assign);
      code_expressiont code_exp(assign);
      block.move(code_exp);
    }

    // enter struct scope
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_type.get(ID_name));

    // find name of constructor
    const struct_typet::componentst &components=
      struct_type.components();

    irep_idt constructor_name;

    for(const auto &c : components)
    {
      const typet &type = c.type();

      if(
        !c.get_bool(ID_from_base) && type.id() == ID_code &&
        to_code_type(type).return_type().id() == ID_constructor)
      {
        constructor_name = c.get_base_name();
        break;
      }
    }

    // there is always a constructor for non-PODs
    assert(constructor_name!="");

    side_effect_expr_function_callt function_call(
      cpp_namet(constructor_name, source_location).as_expr(),
      operands_tc);

    function_call.add_source_location()=source_location;

    typecheck_side_effect_function_call(function_call);
    assert(function_call.get(ID_statement)==ID_temporary_object);

    exprt &initializer =
      static_cast<exprt &>(function_call.add(ID_initializer));

    assert(initializer.id()==ID_code &&
           initializer.get(ID_statement)==ID_expression);

    side_effect_expr_function_callt &func_ini=
      to_side_effect_expr_function_call(initializer.op0());

    exprt &tmp_this=func_ini.arguments().front();
    DATA_INVARIANT(
      to_address_of_expr(tmp_this).object().id() == ID_new_object,
      "expected new_object operand in address_of expression");

    tmp_this=address_of_exprt(object_tc);

    const auto &initializer_code=to_code(initializer);

    if(block.statements().empty())
      return initializer_code;
    else
    {
      block.add(initializer_code);
      return std::move(block);
    }
  }
  else
    UNREACHABLE;

  return {};
}

void cpp_typecheckt::new_temporary(
  const source_locationt &source_location,
  const typet &type,
  const exprt::operandst &ops,
  exprt &temporary)
{
  // create temporary object
  exprt tmp_object_expr=exprt(ID_side_effect, type);
  tmp_object_expr.set(ID_statement, ID_temporary_object);
  tmp_object_expr.add_source_location()= source_location;

  exprt new_object(ID_new_object);
  new_object.add_source_location()=tmp_object_expr.source_location();
  new_object.set(ID_C_lvalue, true);
  new_object.type()=tmp_object_expr.type();

  already_typechecked(new_object);

  auto new_code = cpp_constructor(source_location, new_object, ops);

  if(new_code.has_value())
  {
    if(new_code->get_statement() == ID_assign)
      tmp_object_expr.move_to_operands(new_code->op1());
    else
      tmp_object_expr.add(ID_initializer) = *new_code;
  }

  temporary.swap(tmp_object_expr);
}

void cpp_typecheckt::new_temporary(
  const source_locationt &source_location,
  const typet &type,
  const exprt &op,
  exprt &temporary)
{
  exprt::operandst ops;
  ops.push_back(op);
  new_temporary(source_location, type, ops, temporary);
}
