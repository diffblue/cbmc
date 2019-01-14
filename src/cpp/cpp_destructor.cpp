/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/arith_tools.h>

#include <util/c_types.h>

/// \return typechecked code
optionalt<codet> cpp_typecheckt::cpp_destructor(
  const source_locationt &source_location,
  const exprt &object)
{
  codet new_code;
  new_code.add_source_location()=source_location;

  elaborate_class_template(object.type());

  typet tmp_type(follow(object.type()));

  assert(!is_reference(tmp_type));

  // PODs don't need a destructor
  if(cpp_is_pod(tmp_type))
    return {};

  if(tmp_type.id()==ID_array)
  {
    const exprt &size_expr=
      to_array_type(tmp_type).size();

    if(size_expr.id() == ID_infinity)
      return {}; // don't initialize

    exprt tmp_size=size_expr;
    make_constant_index(tmp_size);

    mp_integer s;
    if(to_integer(to_constant_expr(tmp_size), s))
    {
      error().source_location=source_location;
      error() << "array size `" << to_string(size_expr)
              << "' is not a constant" << eom;
      throw 0;
    }

    new_code.type().id(ID_code);
    new_code.add_source_location()=source_location;
    new_code.set_statement(ID_block);

    // for each element of the array, call the destructor
    for(mp_integer i=0; i < s; ++i)
    {
      exprt constant=from_integer(i, index_type());
      constant.add_source_location()=source_location;

      index_exprt index(object, constant);
      index.add_source_location()=source_location;

      auto i_code = cpp_destructor(source_location, index);
      if(i_code.has_value())
        new_code.add_to_operands(std::move(i_code.value()));
    }
  }
  else
  {
    const struct_typet &struct_type=
      to_struct_type(tmp_type);

    // enter struct scope
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_type.get(ID_name));

    // find name of destructor
    const struct_typet::componentst &components=
      struct_type.components();

    irep_idt dtor_name;

    for(const auto &c : components)
    {
      const typet &type = c.type();

      if(
        !c.get_bool(ID_from_base) && type.id() == ID_code &&
        to_code_type(type).return_type().id() == ID_destructor)
      {
        dtor_name = c.get_base_name();
        break;
      }
    }

    // there is always a destructor for non-PODs
    assert(dtor_name!="");

    cpp_namet cpp_name(dtor_name, source_location);

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cpp_name;
    member.copy_to_operands(object);

    side_effect_expr_function_callt function_call;
    function_call.add_source_location()=source_location;
    function_call.function().swap(member);

    typecheck_side_effect_function_call(function_call);
    already_typechecked(function_call);

    new_code = code_expressiont(function_call);
    new_code.add_source_location() = source_location;
  }

  return new_code;
}
