/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <expr_util.h>
#include <arith_tools.h>
#include <std_expr.h>
#include <simplify_expr_class.h>

#include <ansi-c/c_types.h>
#include <ansi-c/c_sizeof.h>

#include "cpp_typecheck.h"
#include "cpp_util.h"

/*******************************************************************\

Function: cpp_typecheckt::convert_initializer

  Inputs:

 Outputs:

 Purpose: Initialize an object with a value

\*******************************************************************/

void cpp_typecheckt::convert_initializer(symbolt &symbol)
{
  // this is needed for template arguments that are types

  if(symbol.is_type)
  {
    if(symbol.value.is_nil()) return;

    if(symbol.value.id()!=ID_type)
    {
      err_location(symbol.location);
      str << "expected type as initializer for `"
          << symbol.base_name << "'";
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
      err_location(symbol.location);
      str << "`" << symbol.base_name
          << "' is declared as reference but is not initialized";
      throw 0;
    }

    // done
    return;
  }

  // we do have an initializer

  if(is_reference(symbol.type))
  {
    typecheck_expr(symbol.value);
    reference_initializer(symbol.value, symbol.type);
  }
  else if(cpp_is_pod(symbol.type))
  {
    if(symbol.type.id() == ID_pointer &&
       symbol.type.subtype().id() == ID_code &&
       symbol.value.id() == ID_address_of &&
       symbol.value.op0().id() == ID_cpp_name)
    {
      // initialization of a function pointer with
      // the address of a function: use pointer type information
      // for the sake of overload resolution

      cpp_typecheck_fargst fargs;
      fargs.in_use = true;

      const code_typet &code_type=to_code_type(symbol.type.subtype());

      for(code_typet::argumentst::const_iterator
          ait=code_type.arguments().begin();
          ait!=code_type.arguments().end();
          ait++)
      {
        exprt new_object("new_object");
        new_object.set(ID_C_lvalue, true);
        new_object.type() = ait->type();

        if(ait->get(ID_C_base_name)==ID_this)
        {
          fargs.has_object = true;
          new_object.type() = ait->type().subtype();
        }

        fargs.operands.push_back(new_object);
      }

      exprt resolved_expr=resolve(
        to_cpp_name(static_cast<irept &>(symbol.value.op0())),
        cpp_typecheck_resolvet::BOTH, fargs);

      assert(symbol.type.subtype() == resolved_expr.type());

      if(resolved_expr.id()==ID_symbol)
      {
        symbol.value=  
          address_of_exprt(resolved_expr);
      }
      else if(resolved_expr.id()==ID_member)
      {
        symbol.value =
          address_of_exprt(symbol_expr(lookup(resolved_expr.get(ID_component_name))));

        symbol.value.type().add("to-member") = resolved_expr.op0().type();
      }
      else
        assert(false);
      
      if(symbol.type != symbol.value.type())
      {
        err_location(symbol.location);
        str << "conversion from `"
            << to_string(symbol.value.type()) << "' to `"
            << to_string(symbol.type) << "' ";
        throw 0;
      }

      return;
    }

    typecheck_expr(symbol.value);
    
    if(symbol.value.id()==ID_initializer_list ||
       symbol.value.id()==ID_string_constant)
    {
      do_initializer(symbol.value, symbol.type, true);
      
      if(symbol.type.id()==ID_incomplete_array)
        symbol.type=symbol.value.type();
    }
    else
      implicit_typecast(symbol.value, symbol.type);

    simplify_exprt simplify(*this);
    exprt tmp_value = symbol.value;
    if(!simplify.simplify(tmp_value))
      symbol.value.swap(tmp_value);
  }
  else
  {
    // we need a constructor

    symbol_exprt expr_symbol(symbol.name, symbol.type);
    already_typechecked(expr_symbol);

    exprt::operandst ops;
    ops.push_back(symbol.value);

    symbol.value = cpp_constructor(
      symbol.value.location(),
      expr_symbol,
      ops);
  }
}

/*******************************************************************\

Function: cpp_typecheckt::zero_initializer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::zero_initializer(
  const exprt &object,
  const typet &type,
  const locationt &location,
  exprt::operandst &ops)
{
  const typet &final_type=follow(type);

  if(final_type.id()==ID_struct)
  {
    std::list<codet> lst;

    forall_irep(cit, final_type.find(ID_components).get_sub())
    {
      const exprt &component=static_cast<const exprt &>(*cit);

      if(component.type().id()==ID_code)
        continue;

      if(component.get_bool(ID_is_type))
        continue;

      if(component.get_bool(ID_is_static))
        continue;

      exprt member(ID_member);
      member.copy_to_operands(object);
      member.set(ID_component_name, component.get(ID_name));

      // recursive call
      zero_initializer(member, component.type(), location, ops);
    }
  }
  else if(final_type.id()==ID_array)
  {
    if(cpp_is_pod(final_type.subtype()))
    {
      exprt value=
        c_typecheck_baset::zero_initializer(final_type, location);

      exprt obj=object;
      typecheck_expr(obj);

      code_assignt assign;
      assign.lhs()=obj;
      assign.rhs()=value;
      assign.location()=location;
      ops.push_back(assign);
    }
    else
    {
      const array_typet &array_type=to_array_type(type);
      const exprt &size_expr=array_type.size();

      if(size_expr.id()=="infinity")
        return; // don't initialize

      mp_integer size;

      bool to_int=to_integer(size_expr, size);
      assert(!to_int);
      assert(size>=0);

      exprt::operandst empty_operands;
      for(mp_integer i=0; i<size; ++i)
      {
        exprt index(ID_index);
        index.copy_to_operands(object, from_integer(i, int_type()));
        zero_initializer(index, array_type.subtype(), location, ops);
      }
    }
  }
  else if(final_type.id()==ID_union)
  {
    c_sizeoft so(*this);

    // Select the largest component
    mp_integer comp_size=0;

    exprt comp;
    comp.make_nil();

    forall_irep(it, final_type.find(ID_components).get_sub())
    {
      const exprt &component=static_cast<const exprt &>(*it);

      assert(component.type().is_not_nil());

      if(component.type().id()==ID_code)
        continue;

      exprt exs=so(component.type());

      mp_integer size;
      bool to_int = !to_integer(exs,size);
      assert(to_int);

      if(size>comp_size)
      {
        comp_size=size;
        comp=component;
      }
    }

    if(comp_size>0)
    {
      irept name(ID_name);
      name.set(ID_identifier, comp.get(ID_base_name));
      name.set(ID_C_location, location);
      
      cpp_namet cpp_name;
      cpp_name.move_to_sub(name);

      exprt member(ID_member);
      member.copy_to_operands(object);
      member.set("component_cpp_name", cpp_name);
      zero_initializer(member, comp.type(), location, ops);
    }
  }
  else if(final_type.id()==ID_c_enum)
  {
    typet enum_type(ID_unsignedbv);
    enum_type.add(ID_width)=final_type.find(ID_width);

    exprt zero(gen_zero(enum_type));
    zero.make_typecast(type);
    already_typechecked(zero);

    code_assignt assign;
    assign.lhs()=object;
    assign.rhs()=zero;
    assign.location()=location;

    typecheck_expr(assign.lhs());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
  else if(final_type.id()==ID_incomplete_struct ||
          final_type.id()==ID_incomplete_union)
  {
    err_location(location);
    str << "cannot zero-initialize incomplete compound";
    throw 0;
  }
  else
  {
    assert(gen_zero(final_type).is_not_nil());

    code_assignt assign;
    assign.lhs()=object;
    assign.rhs()=gen_zero(final_type);
    assign.location()=location;

    typecheck_expr(assign.op0());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
}
