/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include "require_type.h"

#include <testing-utils/catch.hpp>
#include <util/base_type.h>

/// Checks a type is a pointer type optionally with a specific subtype
/// \param type: The type to check
/// \param subtype: An optional subtype. If provided, checks the subtype of the
///   pointer is this.
/// \return A cast to pointer_typet version of type
pointer_typet require_type::require_pointer(
  const typet &type,
  const optionalt<typet> &subtype)
{
  REQUIRE(type.id() == ID_pointer);
  const pointer_typet &pointer = to_pointer_type(type);

  if(subtype)
  {
    // TODO: use base_type_eq
    REQUIRE(pointer.subtype() == subtype.value());
  }
  return pointer;
}

/// Checks a struct like type has a component with a specific name
/// \param struct_type: The structure that should have the component
/// \param component_name: The name of the component
/// \return The component with the specified name
struct_union_typet::componentt require_type::require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name)
{
  const auto &componet = std::find_if(
    struct_type.components().begin(),
    struct_type.components().end(),
    [&component_name](const struct_union_typet::componentt &component) {
      return component.get_name() == component_name;
    });

  REQUIRE(componet != struct_type.components().end());
  return *componet;
}

/// Checks a type is a code_type (i.e. a function)
/// \param type: The type to check
/// \return The cast version of the type code_type
code_typet require_type::require_code(const typet &type)
{
  REQUIRE(type.id() == ID_code);
  return to_code_type(type);
}

/// Verify a given type is an code_typet, and that the code it represents
/// accepts a given number of parameters
/// \param type The type to check
/// \param num_params check the the given code_typet expects this
/// number of parameters
/// \return The type cast to a code_typet
code_typet require_type::require_code(
  const typet &type,
  const size_t num_params)
{
  code_typet code_type=require_code(type);
  REQUIRE(code_type.parameters().size()==num_params);
  return code_type;
}

/// Verify that a function has a parameter of a specific name.
/// \param function_type: The type of the function
/// \param param_name: The name of the parameter
/// \return: A reference to the parameter structure corresponding to this
///   parameter name.
code_typet::parametert require_type::require_parameter(
  const code_typet &function_type,
  const irep_idt &param_name)
{
  const auto param = std::find_if(
    function_type.parameters().begin(),
    function_type.parameters().end(),
    [&param_name](const code_typet::parametert param) {
      return param.get_base_name() == param_name;
    });

  REQUIRE(param != function_type.parameters().end());
  return *param;
}

/// Verify a given type is a java_generic_type, optionally checking
/// that it's associated type variables match a given set of identifiers
/// \param type The type to check
/// \param type_variables An optional set of type variable identifiers which
/// should be expected as the type parameters of the generic type.
/// \return The given type, cast to a java_generic_typet
const java_generic_typet &require_type::require_java_generic_type_variables(
  const typet &type,
  const optionalt<std::initializer_list<irep_idt>> &type_variables)
{
  REQUIRE(is_java_generic_type(type));
  const java_generic_typet &generic_type=to_java_generic_type(type);
  if(type_variables)
  {
    const java_generic_typet::generic_type_variablest &generic_type_vars=
      generic_type.generic_type_variables();
    REQUIRE(generic_type_vars.size()==type_variables.value().size());
    REQUIRE(
      std::equal(
        type_variables->begin(),
        type_variables->end(),
        generic_type_vars.begin(),
        [](const irep_idt &type_var_name, const java_generic_parametert &param)
        {
          REQUIRE(!is_java_generic_inst_parameter((param)));
          return param.type_variable().get_identifier()==type_var_name;
        }));
  }

  return generic_type;
}

/// Verify a given type is a java_generic_type, optionally checking
/// that it's associated type variables match a given set of identifiers
/// \param type The type to check
/// \param type_variables An optional set of type variable identifiers which
/// should be expected as the type parameters of the generic type.
/// \return The given type, cast to a java_generic_typet
const java_generic_typet
&require_type::require_java_generic_type_instantiations(
  const typet &type,
  const optionalt<std::initializer_list<irep_idt>> &type_instantiations)
{
  REQUIRE(is_java_generic_type(type));
  const java_generic_typet &generic_type=to_java_generic_type(type);
  if(type_instantiations)
  {
    const java_generic_typet::generic_type_variablest &generic_type_vars=
      generic_type.generic_type_variables();
    REQUIRE(generic_type_vars.size()==type_instantiations.value().size());
    REQUIRE(
      std::equal(
        type_instantiations->begin(),
        type_instantiations->end(),
        generic_type_vars.begin(),
        [](const irep_idt &type_id, const java_generic_parametert &param)
        {
          REQUIRE(is_java_generic_inst_parameter((param)));
          return param.subtype()==symbol_typet(type_id);
        }));
  }


  return generic_type;
}

/// Verify a given type is a java_generic_parameter, optionally checking
/// that it's associated type variables match a given set of identifiers
/// \param type The type to check
/// \param type_variables An optional set of type variable identifiers which
/// should be expected as the type parameters of the generic type.
/// \return The given type, cast to a java_generic_typet
const java_generic_parametert
&require_type::require_java_generic_parameter_variables(
  const typet &type,
  const optionalt<irep_idt> &type_variable)
{
  REQUIRE(is_java_generic_parameter(type));
  const java_generic_parametert &generic_param=to_java_generic_parameter(type);
  if(type_variable)
  {
    const java_generic_parametert::type_variablet &generic_type_var=
      generic_param.type_variable();
    REQUIRE(!is_java_generic_inst_parameter((generic_param)));
    REQUIRE(generic_type_var.get_identifier()==type_variable.value());
  }

  return generic_param;
}

const typet &require_type::require_java_non_generic_type(
  const typet &type,
  const optionalt<irep_idt> &expect_type)
{
  REQUIRE(!is_java_generic_parameter(type));
  REQUIRE(!is_java_generic_type(type));
  REQUIRE(!is_java_generic_inst_parameter(type));
  if(expect_type)
    REQUIRE(type.subtype()==symbol_typet(expect_type.value()));
  return type;
}
