/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>

#include "cpp_typecheck.h"

/// \param source_location: source location for generated code
/// \param object: non-typechecked object
/// \param operands: non-typechecked operands
/// \return typechecked code
std::optional<codet> cpp_typecheckt::cpp_constructor(
  const source_locationt &source_location,
  const exprt &object,
  const exprt::operandst &operands)
{
  exprt object_tc = object;

  typecheck_expr(object_tc);

  elaborate_class_template(object_tc.type());

  CHECK_RETURN(!is_reference(object_tc.type()));

  if(object_tc.type().id() == ID_array)
  {
    // We allow only one operand and it must be tagged with '#array_ini'.
    // Note that the operand is an array that is used for copy-initialization.
    // In the general case, a program is not allowed to use this form of
    // construct. This way of initializing an array is used internally only.
    // The purpose of the tag #array_ini is to rule out ill-formed
    // programs.

    if(!operands.empty() && !operands.front().get_bool(ID_C_array_ini))
    {
      // C++11 brace-enclosed initialization: build an array expression
      // from the individual operands and assign it.
      const auto &array_type = to_array_type(object_tc.type());
      array_exprt array_val(operands, array_type);
      array_val.add_source_location() = source_location;
      array_val.set(ID_C_array_ini, true);
      return cpp_constructor(source_location, object, {std::move(array_val)});
    }

    DATA_INVARIANT(
      operands.empty() || operands.size() == 1,
      "array constructor must have at most one operand");

    if(operands.empty() && cpp_is_pod(object_tc.type()))
      return {};

    const exprt &size_expr = to_array_type(object_tc.type()).size();

    if(size_expr.id() == ID_infinity)
      return {}; // don't initialize

    exprt tmp_size = size_expr;
    make_constant_index(tmp_size);

    mp_integer s;
    if(to_integer(to_constant_expr(tmp_size), s))
    {
      error().source_location = source_location;
      error() << "array size '" << to_string(size_expr) << "' is not a constant"
              << eom;
      throw 0;
    }

    /*if(cpp_is_pod(object_tc.type()))
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
      for(mp_integer i = 0; i < s; ++i)
      {
        exprt::operandst tmp_operands;

        exprt constant = from_integer(i, c_index_type());
        constant.add_source_location() = source_location;

        index_exprt index = index_exprt(object_tc, constant);
        index.add_source_location() = source_location;

        if(!operands.empty())
        {
          index_exprt operand(operands.front(), constant);
          operand.add_source_location() = source_location;
          tmp_operands.push_back(operand);
        }

        auto i_code = cpp_constructor(source_location, index, tmp_operands);

        if(i_code.has_value())
          new_code.add(std::move(i_code.value()));
      }
      return std::move(new_code);
    }
  }
  else if(cpp_is_pod(object_tc.type()))
  {
    exprt::operandst operands_tc = operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    if(operands_tc.empty())
    {
      // C++11: apply default member initializers for POD types
      if(object_tc.type().id() == ID_struct_tag)
      {
        const struct_typet &struct_type =
          follow_tag(to_struct_tag_type(object_tc.type()));
        code_blockt block;
        for(const auto &comp : struct_type.components())
        {
          if(
            comp.get_bool(ID_is_type) || comp.get_bool(ID_is_static) ||
            comp.type().id() == ID_code)
            continue;
          const irept &default_val = comp.find(ID_C_default_value);
          if(default_val.is_not_nil())
          {
            exprt val = static_cast<const exprt &>(default_val);
            typecheck_expr(val);
            if(val.type() != comp.type())
              val = typecast_exprt(val, comp.type());
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);
            block.add(code_frontend_assignt(std::move(member), std::move(val)));
          }
        }
        if(!block.statements().empty())
          return std::move(block);
      }
      // a POD is NOT initialized
      return {};
    }
    else if(operands_tc.size() == 1)
    {
      // Override constantness
      object_tc.type().set(ID_C_constant, false);
      object_tc.set(ID_C_lvalue, true);
      side_effect_expr_assignt assign(
        object_tc, operands_tc.front(), typet(), source_location);
      typecheck_side_effect_assignment(assign);
      return code_expressiont(std::move(assign));
    }
    else
    {
      // C++20 aggregate parenthesized initialization
      if(object_tc.type().id() == ID_struct_tag)
      {
        const struct_typet &struct_type =
          follow_tag(to_struct_tag_type(object_tc.type()));
        const auto &components = struct_type.components();
        code_blockt block;
        std::size_t idx = 0;
        for(const auto &comp : components)
        {
          if(
            comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
            comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
            continue;
          if(idx < operands_tc.size())
          {
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);
            exprt val =
              typecast_exprt::conditional_cast(operands_tc[idx], comp.type());
            side_effect_expr_assignt assign(
              std::move(member), std::move(val), typet(), source_location);
            typecheck_side_effect_assignment(assign);
            block.add(code_expressiont(std::move(assign)));
          }
          ++idx;
        }
        return std::move(block);
      }
      error().source_location = source_location;
      error() << "initialization of POD requires one argument, "
                 "but got "
              << operands.size() << eom;
      throw 0;
    }
  }
  else if(object_tc.type().id() == ID_union_tag)
  {
    UNREACHABLE; // Todo: union
  }
  else if(object_tc.type().id() == ID_struct_tag)
  {
    exprt::operandst operands_tc = operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    const struct_typet &struct_type =
      follow_tag(to_struct_tag_type(object_tc.type()));

    // C++17 aggregate initialization with base classes:
    // If the struct has bases but no user-declared constructors and
    // multiple operands are provided, do aggregate initialization.
    if(!struct_type.bases().empty() && operands_tc.size() >= 2)
    {
      bool has_user_ctor = false;
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &ct = to_code_type(c.type());
        if(ct.return_type().id() != ID_constructor)
          continue;
        // Skip default ctor (this only) and copy/move ctor
        if(ct.parameters().size() <= 1)
          continue;
        if(
          ct.parameters().size() == 2 &&
          is_reference(ct.parameters()[1].type()))
          continue;
        has_user_ctor = true;
        break;
      }
      if(!has_user_ctor)
      {
        code_blockt block;
        std::size_t idx = 0;
        // Initialize base class subobjects: for each base, the
        // corresponding operand initializes the from_base data members.
        for(std::size_t b = 0; b < struct_type.bases().size(); ++b)
        {
          if(idx >= operands_tc.size())
            break;
          // Collect from_base data members belonging to this base
          exprt::operandst base_ops;
          if(operands_tc[idx].id() == ID_initializer_list)
            base_ops = operands_tc[idx].operands();
          else
            base_ops.push_back(operands_tc[idx]);
          std::size_t bidx = 0;
          for(const auto &comp : struct_type.components())
          {
            if(
              !comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
              comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
              continue;
            if(bidx >= base_ops.size())
              break;
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);
            exprt val =
              typecast_exprt::conditional_cast(base_ops[bidx], comp.type());
            side_effect_expr_assignt assign(
              std::move(member), std::move(val), typet(), source_location);
            typecheck_side_effect_assignment(assign);
            block.add(code_expressiont(std::move(assign)));
            ++bidx;
          }
          ++idx;
        }
        // Initialize non-static data members
        for(const auto &comp : struct_type.components())
        {
          if(
            comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
            comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
            continue;
          if(idx >= operands_tc.size())
            break;
          member_exprt member(object_tc, comp.get_name(), comp.type());
          member.set(ID_C_lvalue, true);
          exprt val =
            typecast_exprt::conditional_cast(operands_tc[idx], comp.type());
          side_effect_expr_assignt assign(
            std::move(member), std::move(val), typet(), source_location);
          typecheck_side_effect_assignment(assign);
          block.add(code_expressiont(std::move(assign)));
          ++idx;
        }
        return std::move(block);
      }
    }

    // set most-derived bits
    code_blockt block;
    for(const auto &component : struct_type.components())
    {
      if(component.get_base_name() != "@most_derived")
        continue;

      member_exprt member(object_tc, component.get_name(), bool_typet());
      member.add_source_location() = source_location;
      member.set(ID_C_lvalue, object_tc.get_bool(ID_C_lvalue));

      exprt val = false_exprt();

      if(!component.get_bool(ID_from_base))
        val = true_exprt();

      side_effect_expr_assignt assign(
        std::move(member), std::move(val), typet(), source_location);

      typecheck_side_effect_assignment(assign);

      block.add(code_expressiont(std::move(assign)));
    }

    // enter struct scope
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_type.get(ID_name));

    // find name of constructor
    const struct_typet::componentst &components = struct_type.components();

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

    INVARIANT(!constructor_name.empty(), "non-PODs should have a constructor");

    side_effect_expr_function_callt function_call(
      cpp_namet(constructor_name, source_location).as_expr(),
      operands_tc,
      uninitialized_typet(),
      source_location);

    typecheck_side_effect_function_call(function_call);

    if(function_call.get(ID_statement) != ID_temporary_object)
    {
      error().source_location = source_location;
      error() << "constructor call did not resolve to temporary object" << eom;
      throw 0;
    }

    exprt &initializer =
      static_cast<exprt &>(function_call.add(ID_initializer));

    DATA_INVARIANT(
      initializer.id() == ID_code &&
        initializer.get(ID_statement) == ID_expression,
      "initializer must be expression statement");

    auto &statement_expr = to_code_expression(to_code(initializer));

    side_effect_expr_function_callt &func_ini =
      to_side_effect_expr_function_call(statement_expr.expression());

    exprt &tmp_this = func_ini.arguments().front();
    DATA_INVARIANT(
      to_address_of_expr(tmp_this).object().id() == ID_new_object,
      "expected new_object operand in address_of expression");

    tmp_this = address_of_exprt(object_tc);

    const auto &initializer_code = to_code(initializer);

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
  side_effect_exprt tmp_object_expr(ID_temporary_object, type, source_location);
  tmp_object_expr.set(ID_mode, ID_cpp);

  exprt new_object(ID_new_object);
  new_object.add_source_location() = tmp_object_expr.source_location();
  new_object.set(ID_C_lvalue, true);
  new_object.type() = tmp_object_expr.type();

  already_typechecked_exprt::make_already_typechecked(new_object);

  auto new_code = cpp_constructor(source_location, new_object, ops);

  if(new_code.has_value())
  {
    if(new_code->get_statement() == ID_assign)
      tmp_object_expr.add_to_operands(std::move(new_code->op1()));
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
