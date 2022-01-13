/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>

#include "cpp_convert_type.h"
#include "cpp_typecheck_fargs.h"

/// Initialize an object with a value
void cpp_typecheckt::convert_initializer(symbolt &symbol)
{
  // this is needed for template arguments that are types

  if(symbol.is_type)
  {
    if(symbol.value.is_nil())
      return;

    if(symbol.value.id()!=ID_type)
    {
      error().source_location=symbol.location;
      error() << "expected type as initializer for '" << symbol.base_name << "'"
              << eom;
      throw 0;
    }

    typecheck_type(symbol.value.type());

    return;
  }

  // do we have an initializer?
  if(symbol.value.is_nil())
  {
    // do we need one?
    if(is_reference(symbol.type))
    {
      error().source_location=symbol.location;
      error() << "'" << symbol.base_name
              << "' is declared as reference but is not initialized" << eom;
      throw 0;
    }

    // done
    return;
  }

  // we do have an initializer

  if(is_reference(symbol.type))
  {
    typecheck_expr(symbol.value);

    if(has_auto(symbol.type))
    {
      cpp_convert_auto(symbol.type, symbol.value.type(), get_message_handler());
      typecheck_type(symbol.type);
      implicit_typecast(symbol.value, symbol.type);
    }

    reference_initializer(symbol.value, symbol.type);
  }
  else if(cpp_is_pod(symbol.type))
  {
    if(
      symbol.type.id() == ID_pointer && symbol.type.subtype().id() == ID_code &&
      symbol.value.id() == ID_address_of &&
      to_address_of_expr(symbol.value).object().id() == ID_cpp_name)
    {
      // initialization of a function pointer with
      // the address of a function: use pointer type information
      // for the sake of overload resolution

      cpp_typecheck_fargst fargs;
      fargs.in_use = true;

      const code_typet &code_type=to_code_type(symbol.type.subtype());

      for(const auto &parameter : code_type.parameters())
      {
        exprt new_object(ID_new_object, parameter.type());
        new_object.set(ID_C_lvalue, true);

        if(parameter.get_this())
        {
          fargs.has_object = true;
          new_object.type() = parameter.type().subtype();
        }

        fargs.operands.push_back(new_object);
      }

      exprt resolved_expr = resolve(
        to_cpp_name(
          static_cast<irept &>(to_address_of_expr(symbol.value).object())),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      assert(symbol.type.subtype() == resolved_expr.type());

      if(resolved_expr.id()==ID_symbol)
      {
        symbol.value=
          address_of_exprt(resolved_expr);
      }
      else if(resolved_expr.id()==ID_member)
      {
        symbol.value =
          address_of_exprt(
            lookup(resolved_expr.get(ID_component_name)).symbol_expr());

        symbol.value.type().add(ID_to_member) =
          to_member_expr(resolved_expr).compound().type();
      }
      else
        UNREACHABLE;

      if(symbol.type != symbol.value.type())
      {
        error().source_location=symbol.location;
        error() << "conversion from '" << to_string(symbol.value.type())
                << "' to '" << to_string(symbol.type) << "' " << eom;
        throw 0;
      }

      return;
    }

    typecheck_expr(symbol.value);

    if(symbol.value.type().find(ID_to_member).is_not_nil())
      symbol.type.add(ID_to_member) = symbol.value.type().find(ID_to_member);

    if(symbol.value.id()==ID_initializer_list ||
       symbol.value.id()==ID_string_constant)
    {
      do_initializer(symbol.value, symbol.type, true);

      if(symbol.type.find(ID_size).is_nil())
        symbol.type=symbol.value.type();
    }
    else if(has_auto(symbol.type))
    {
      cpp_convert_auto(symbol.type, symbol.value.type(), get_message_handler());
      typecheck_type(symbol.type);
      implicit_typecast(symbol.value, symbol.type);
    }
    else
      implicit_typecast(symbol.value, symbol.type);

    #if 0
    simplify_exprt simplify(*this);
    exprt tmp_value = symbol.value;
    if(!simplify.simplify(tmp_value))
      symbol.value.swap(tmp_value);
    #endif
  }
  else
  {
    // we need a constructor

    symbol_exprt expr_symbol(symbol.name, symbol.type);
    already_typechecked_exprt::make_already_typechecked(expr_symbol);

    exprt::operandst ops;
    ops.push_back(symbol.value);

    auto constructor =
      cpp_constructor(symbol.value.source_location(), expr_symbol, ops);

    if(constructor.has_value())
      symbol.value = constructor.value();
    else
      symbol.value = nil_exprt();
  }
}

void cpp_typecheckt::zero_initializer(
  const exprt &object,
  const typet &type,
  const source_locationt &source_location,
  exprt::operandst &ops)
{
  const typet &final_type=follow(type);

  if(final_type.id()==ID_struct)
  {
    const auto &struct_type = to_struct_type(final_type);

    if(struct_type.is_incomplete())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize incomplete struct" << eom;
      throw 0;
    }

    for(const auto &component : struct_type.components())
    {
      if(component.type().id()==ID_code)
        continue;

      if(component.get_bool(ID_is_type))
        continue;

      if(component.get_bool(ID_is_static))
        continue;

      member_exprt member(object, component.get_name(), component.type());

      // recursive call
      zero_initializer(member, component.type(), source_location, ops);
    }
  }
  else if(final_type.id()==ID_array &&
          !cpp_is_pod(final_type.subtype()))
  {
    const array_typet &array_type=to_array_type(type);
    const exprt &size_expr=array_type.size();

    if(size_expr.id()==ID_infinity)
      return; // don't initialize

    const mp_integer size =
      numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
    CHECK_RETURN(size>=0);

    exprt::operandst empty_operands;
    for(mp_integer i=0; i<size; ++i)
    {
      index_exprt index(
        object, from_integer(i, c_index_type()), array_type.subtype());
      zero_initializer(index, array_type.subtype(), source_location, ops);
    }
  }
  else if(final_type.id()==ID_union)
  {
    const auto &union_type = to_union_type(final_type);

    if(union_type.is_incomplete())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize incomplete union" << eom;
      throw 0;
    }

    // Select the largest component for zero-initialization
    mp_integer max_comp_size=0;

    union_typet::componentt comp;

    for(const auto &component : union_type.components())
    {
      assert(component.type().is_not_nil());

      if(component.type().id()==ID_code)
        continue;

      auto component_size_opt = size_of_expr(component.type(), *this);

      const auto size_int =
        numeric_cast<mp_integer>(component_size_opt.value_or(nil_exprt()));
      if(size_int.has_value())
      {
        if(*size_int > max_comp_size)
        {
          max_comp_size = *size_int;
          comp=component;
        }
      }
    }

    if(max_comp_size>0)
    {
      const cpp_namet cpp_name(comp.get_base_name(), source_location);

      exprt member(ID_member);
      member.copy_to_operands(object);
      member.set(ID_component_cpp_name, cpp_name);
      zero_initializer(member, comp.type(), source_location, ops);
    }
  }
  else if(final_type.id()==ID_c_enum)
  {
    const unsignedbv_typet enum_type(
      to_bitvector_type(final_type.subtype()).get_width());

    exprt zero =
      typecast_exprt::conditional_cast(from_integer(0, enum_type), type);
    already_typechecked_exprt::make_already_typechecked(zero);

    code_frontend_assignt assign;
    assign.lhs()=object;
    assign.rhs()=zero;
    assign.add_source_location()=source_location;

    typecheck_expr(assign.lhs());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked_exprt::make_already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
  else
  {
    const auto value = ::zero_initializer(final_type, source_location, *this);
    if(!value.has_value())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize '" << to_string(final_type) << "'"
              << eom;
      throw 0;
    }

    code_frontend_assignt assign(object, *value);
    assign.add_source_location()=source_location;

    typecheck_expr(assign.lhs());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked_exprt::make_already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
}
