/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::cpp_destructor

  Inputs:

 Outputs: NOT typechecked code

 Purpose:

\*******************************************************************/

codet cpp_typecheckt::cpp_destructor(
  const source_locationt &source_location,
  const typet &type,
  const exprt &object)
{
  codet new_code;
  new_code.add_source_location()=source_location;

  typet tmp_type(type);
  follow_symbol(tmp_type);

  assert(!is_reference(tmp_type));

  // PODs don't need a destructor
  if(cpp_is_pod(tmp_type))
  {
    new_code.make_nil();
    return new_code;
  }

  if(tmp_type.id()==ID_array)
  {
    const exprt &size_expr=
      to_array_type(tmp_type).size();

    if(size_expr.id()=="infinity")
    {
      // don't initialize
      new_code.make_nil();
      return new_code;
    }
    
    exprt tmp_size=size_expr;
    make_constant_index(tmp_size);

    mp_integer s;
    if(to_integer(tmp_size, s))
    {
      err_location(source_location);
      str << "array size `" << to_string(size_expr)
          << "' is not a constant";
      throw 0;
    }

    new_code.type().id(ID_code);
    new_code.add_source_location()=source_location;
    new_code.set_statement(ID_block);

    // for each element of the array, call the destructor
    for(mp_integer i = 0; i < s; ++i)
    {
      exprt constant=from_integer(i, index_type());
      constant.add_source_location()=source_location;

      exprt index(ID_index);
      index.copy_to_operands(object);
      index.copy_to_operands(constant);
      index.add_source_location()=source_location;

      exprt i_code =
        cpp_destructor(source_location, tmp_type.subtype(), index);

      new_code.move_to_operands(i_code);
    }
  }
  else
  {
    const struct_typet &struct_type=
      to_struct_type(tmp_type);

    // find name of destructor
    const struct_typet::componentst &components=
      struct_type.components();

    irep_idt dtor_name;

    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      const typet &type=it->type();

      if(!it->get_bool(ID_from_base) &&
         type.id()==ID_code &&
         type.find(ID_return_type).id()==ID_destructor)
      {
        dtor_name=it->get(ID_base_name);
        break;
      }
    }

    // there is always a destructor for non-PODs
    assert(dtor_name!="");

    const symbolt &symb=lookup(struct_type.get(ID_name));

    irept cpp_name(ID_cpp_name);

    cpp_name.get_sub().push_back(irept(ID_name));
    cpp_name.get_sub().back().set(ID_identifier, symb.base_name);
    cpp_name.get_sub().back().set(ID_C_source_location, source_location);

    cpp_name.get_sub().push_back(irept("::"));

    cpp_name.get_sub().push_back(irept(ID_name));
    cpp_name.get_sub().back().set(ID_identifier, dtor_name);
    cpp_name.get_sub().back().set(ID_C_source_location, source_location);

    exprt member_expr(ID_member);
    member_expr.copy_to_operands(object);
    member_expr.op0().type().set(ID_C_constant, false);
    member_expr.add("component_cpp_name").swap(cpp_name);
    member_expr.add_source_location()=source_location;

    side_effect_expr_function_callt function_call;
    function_call.function()=member_expr;
    function_call.add_source_location()=source_location;

    new_code.set_statement(ID_expression);
    new_code.add_source_location()=source_location;
    new_code.move_to_operands(function_call);
  }

  return new_code;
}

