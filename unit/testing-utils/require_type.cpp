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
/// parameter name.
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

/// Helper function for testing that java_generic_parametert types match
/// a given expectation.
/// \param param The generic parameter to test
/// \param expected The expected value of the parameter
/// \return true if the generic parameter type meets the expectations
bool require_java_generic_parametert_expectation(
  const java_generic_parametert &param,
  const require_type::expected_type_parametert &expected)
{
  switch(expected.kind)
  {
    case require_type::type_parameter_kindt::Var:
      REQUIRE(!is_java_generic_inst_parameter((param)));
      REQUIRE(param.type_variable().get_identifier()==expected.description);
      return true;
    case require_type::type_parameter_kindt::Inst:
      REQUIRE(is_java_generic_inst_parameter((param)));
      REQUIRE(param.subtype()==symbol_typet(expected.description));
      return true;
  }
  // Should be unreachable...
  REQUIRE(false);
  return false;
}


/// Verify a given type is a java_generic_type, optionally checking
/// that it's associated type variables match a given set of identifiers.
/// Expected usage is something like this:
///
/// require_java_generic_type(type,
///                          {{Inst,"java::java.lang.Integer"},{Var,"T"}})
///
/// \param type The type to check
/// \param type_expectations An optional set of type variable kinds
/// and identifiers which should be expected as the type parameters of the
/// given generic type.
/// \return The given type, cast to a java_generic_typet
java_generic_typet require_type::require_java_generic_type(
  const typet &type,
  const optionalt<require_type::expected_type_parameterst> &type_expectations)
{
  REQUIRE(is_java_generic_type(type));
  const java_generic_typet &generic_type=to_java_generic_type(type);
  if(type_expectations)
  {
    const java_generic_typet::generic_type_variablest &generic_type_vars=
      generic_type.generic_type_variables();
    REQUIRE(generic_type_vars.size()==type_expectations->size());
    REQUIRE(
      std::equal(
        generic_type_vars.begin(),
        generic_type_vars.end(),
        type_expectations->begin(),
        require_java_generic_parametert_expectation));
  }

  return generic_type;
}

/// Verify a given type is a java_generic_parameter, optionally checking
/// that it's associated type variables match a given set of expectations.
/// Expected usage is something like this:
///
/// require_java_generic_parameter(parameter, {Inst,"java::java.lang.Integer"})
///
/// or
///
/// require_java_generic_parameter(parameter, {Var,"T"})
///
/// \param type The type to check
/// \param type_expectation An optional description of the identifiers/kinds
/// which / should be expected as the type parameter of the generic parameter.
/// \return The given type, cast to a java_generic_parametert
java_generic_parametert require_type::require_java_generic_parameter(
  const typet &type,
  const optionalt<require_type::expected_type_parametert> &type_expectation)
{
  REQUIRE(is_java_generic_parameter(type));
  const java_generic_parametert &generic_param=to_java_generic_parameter(type);
  if(type_expectation)
  {
    REQUIRE(
      require_java_generic_parametert_expectation(
        generic_param,
        type_expectation.value()));
  }

  return generic_param;
}

/// Test a type to ensure it is not a java generics type.
/// \param type The type to test
/// \param expect_subtype Optionally, also test that the subtype of the given
/// type matches this parameter
/// \return The value passed in the first argument
const typet &require_type::require_java_non_generic_type(
  const typet &type,
  const optionalt<symbol_typet> &expect_subtype)
{
  REQUIRE(!is_java_generic_parameter(type));
  REQUIRE(!is_java_generic_type(type));
  REQUIRE(!is_java_generic_inst_parameter(type));
  if(expect_subtype)
    REQUIRE(type.subtype()==expect_subtype.value());
  return type;
}
