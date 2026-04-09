/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

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

    // C++20: lambda in unevaluated context (decltype).
    // The type carries the lambda function address so that
    // default-initialization produces a valid function pointer.
    const irept &lambda_init = symbol.type.find("#lambda_initializer");
    if(lambda_init.is_not_nil())
    {
      symbol.value = static_cast<const exprt &>(lambda_init);
      return;
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
      // C++17: auto x{v} deduces to decltype(v)
      typet deduced_type = symbol.value.type();
      if(
        symbol.value.id() == ID_initializer_list &&
        symbol.value.operands().size() == 1)
      {
        deduced_type = symbol.value.operands().front().type();
        symbol.value = symbol.value.operands().front();
      }
      cpp_convert_auto(symbol.type, deduced_type, get_message_handler());
      // For auto& in const context: if the initializer is const,
      // the reference must also be const (e.g., auto& x = d; in
      // a const method where d is a const member).
      if(
        is_reference(symbol.type) &&
        symbol.value.type().get_bool(ID_C_constant) &&
        symbol.type.id() == ID_pointer)
      {
        to_pointer_type(symbol.type).base_type().set(ID_C_constant, true);
      }
      typecheck_type(symbol.type);
      implicit_typecast(symbol.value, symbol.type);
    }

    reference_initializer(symbol.value, to_reference_type(symbol.type));
  }
  else if(has_auto(symbol.type) && !is_reference(symbol.type))
  {
    // auto type deduction for non-reference types
    // C++11: auto x = {1, 2, 3} deduces std::initializer_list<int>
    if(
      symbol.value.id() == ID_initializer_list &&
      !symbol.value.operands().empty())
    {
      // Type-check the first element to determine T
      exprt first = symbol.value.operands()[0];
      typecheck_expr(first);
      // Build std::initializer_list<T> type
      // For verification purposes, model as a const array
      symbol.type = array_typet(
        first.type(),
        from_integer(symbol.value.operands().size(), size_type()));
      // Type-check all elements
      exprt::operandst elems;
      for(auto &op : symbol.value.operands())
      {
        typecheck_expr(op);
        implicit_typecast(op, first.type());
        elems.push_back(op);
      }
      symbol.value = array_exprt(std::move(elems), to_array_type(symbol.type));
      return;
    }
    typecheck_expr(symbol.value);

    // decltype(auto): if initializer is a function call returning a
    // reference, deduce the reference type
    if(
      symbol.type.id() == ID_decltype && symbol.type.get_bool("#auto") &&
      symbol.value.id() == ID_dereference &&
      is_reference(to_dereference_expr(symbol.value).pointer().type()))
    {
      const typet &ref_type =
        to_dereference_expr(symbol.value).pointer().type();
      cpp_convert_auto(symbol.type, ref_type, get_message_handler());
      typecheck_type(symbol.type);
      reference_initializer(symbol.value, to_reference_type(symbol.type));
      return;
    }

    cpp_convert_auto(symbol.type, symbol.value.type(), get_message_handler());
    typecheck_type(symbol.type);
    implicit_typecast(symbol.value, symbol.type);
  }
  else if(cpp_is_pod(symbol.type))
  {
    if(
      symbol.type.id() == ID_pointer &&
      to_pointer_type(symbol.type).base_type().id() == ID_code &&
      symbol.value.id() == ID_address_of &&
      to_address_of_expr(symbol.value).object().id() == ID_cpp_name)
    {
      // initialization of a function pointer with
      // the address of a function: use pointer type information
      // for the sake of overload resolution

      cpp_typecheck_fargst fargs;
      fargs.in_use = true;

      const code_typet &code_type =
        to_code_type(to_pointer_type(symbol.type).base_type());

      for(const auto &parameter : code_type.parameters())
      {
        exprt new_object(ID_new_object, parameter.type());
        new_object.set(ID_C_lvalue, true);

        if(parameter.get_this())
        {
          fargs.has_object = true;
          new_object.type() = to_pointer_type(parameter.type()).base_type();
        }

        fargs.operands.push_back(new_object);
      }

      exprt resolved_expr = resolve(
        to_cpp_name(
          static_cast<irept &>(to_address_of_expr(symbol.value).object())),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      // For pointer-to-member-function, the symbol type includes a
      // to_member attribute and the resolved expression may have a
      // different representation. Skip the strict type check when
      // pointer-to-member is involved.
      if(
        symbol.type.find(ID_to_member).is_nil() &&
        to_pointer_type(symbol.type).base_type() != resolved_expr.type())
      {
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          false,
          "symbol type must match",
          symbol.type.pretty(),
          resolved_expr.type().pretty(),
          symbol.location);
      }

      if(resolved_expr.id()==ID_symbol)
      {
        symbol.value=
          address_of_exprt(resolved_expr);

        if(symbol.type.find(ID_to_member).is_not_nil())
          symbol.value.type().add(ID_to_member) =
            symbol.type.find(ID_to_member);
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

    // Aggregate initialization: for braced-init-list on non-POD struct
    // types that have no user-declared constructors (only compiler-
    // generated copy/move constructors), perform member-by-member
    // initialization.  This handles non-POD aggregates such as structs
    // with reference members.
    if(
      symbol.value.id() == ID_initializer_list &&
      symbol.type.id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(symbol.type));

      // Check whether the struct has any non-copy constructor.
      bool has_non_copy_ctor = false;
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &code_type = to_code_type(c.type());
        if(code_type.return_type().id() != ID_constructor)
          continue;
        // Copy constructor: this + const T& (2 parameters)
        // Default constructor: this only (1 parameter)
        const auto &params = code_type.parameters();
        if(params.size() <= 1)
          continue;
        if(params.size() == 2 && is_reference(params[1].type()))
          continue;
        has_non_copy_ctor = true;
        break;
      }

      if(!has_non_copy_ctor)
      {
        const auto &ops = symbol.value.operands();
        std::size_t idx = 0;
        bool aggregate = true;

        // C++17: check if we have base class initializers
        bool has_base_init = struct_type.id() == ID_struct &&
                             !to_struct_type(struct_type).bases().empty();

        if(has_base_init)
        {
          // Convert to constructor-style code that initializes
          // base subobjects and members individually.
          // Copy operands since cpp_constructor may modify symbol.value.
          exprt::operandst ops_copy = symbol.value.operands();
          symbol_exprt sym_expr(symbol.name, symbol.type);
          already_typechecked_exprt::make_already_typechecked(sym_expr);
          auto init =
            cpp_constructor(symbol.value.source_location(), sym_expr, ops_copy);
          if(init.has_value())
          {
            symbol.value = std::move(*init);
            return;
          }
        }

        struct_exprt result({}, symbol.type);
        for(const auto &c : struct_type.components())
        {
          if(
            c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
            c.get_bool(ID_is_static) || c.type().id() == ID_code)
          {
            continue;
          }
          if(c.get_base_name() == "@most_derived")
            continue;
          if(idx < ops.size())
          {
            exprt val = ops[idx++];
            typecheck_expr(val);
            if(is_reference(c.type()))
              reference_initializer(val, to_reference_type(c.type()));
            else
              implicit_typecast(val, c.type());
            result.add_to_operands(std::move(val));
          }
          else
          {
            aggregate = false;
            break;
          }
        }
        if(aggregate)
        {
          symbol.value = std::move(result);
          return;
        }
      }
    }

    symbol_exprt expr_symbol(symbol.name, symbol.type);
    already_typechecked_exprt::make_already_typechecked(expr_symbol);

    exprt::operandst ops;

    // For braced-init-list, first try passing as a single
    // std::initializer_list argument (C++11 [over.match.list]).
    // If that fails, fall back to unpacking the elements as
    // individual constructor arguments.
    if(symbol.value.id() == ID_initializer_list)
    {
      // Try as single initializer_list argument first
      ops.push_back(symbol.value);
      auto constructor =
        cpp_constructor(symbol.value.source_location(), expr_symbol, ops);
      if(constructor.has_value())
      {
        symbol.value = constructor.value();
        return;
      }
      // Fall back to unpacking
      ops = symbol.value.operands();
    }
    else
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
  if(type.id() == ID_struct_tag)
  {
    const auto &struct_type = follow_tag(to_struct_tag_type(type));

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
  else if(
    type.id() == ID_array && !cpp_is_pod(to_array_type(type).element_type()))
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
        object, from_integer(i, c_index_type()), array_type.element_type());
      zero_initializer(index, array_type.element_type(), source_location, ops);
    }
  }
  else if(type.id() == ID_union_tag)
  {
    const auto &union_type = follow_tag(to_union_tag_type(type));

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
      DATA_INVARIANT(component.type().is_not_nil(), "missing component type");

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
  else if(type.id() == ID_c_enum_tag)
  {
    const unsignedbv_typet enum_type(
      to_bitvector_type(follow_tag(to_c_enum_tag_type(type)).underlying_type())
        .get_width());

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
    const auto value = ::zero_initializer(type, source_location, *this);
    if(!value.has_value())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize '" << to_string(type) << "'" << eom;
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
