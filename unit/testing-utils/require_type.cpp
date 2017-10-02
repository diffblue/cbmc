/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific types
/// If the type is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#include "require_type.h"

#include <testing-utils/catch.hpp>

/// Verify a given type is an code_typet, optionally also checking it accepts
/// a givne number of parameters
/// \param type The type to check
/// \param num_params If given, check the the given code_typet expects this
/// number of parameters
/// \param return_type If given, check the return type of the given code_typet
/// matches return_type
/// \return The type cast to a code_typet
const code_typet &require_type::require_code_type(
  const typet &type,
  optionalt<size_t> num_params)
{
  REQUIRE(type.id()==ID_code);
  const code_typet &code_type=to_code_type(type);
  if(num_params)
    REQUIRE(code_type.parameters().size()==num_params.value());
  return code_type;
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
    const optionalt<std::initializer_list<irep_idt>> &type_variables)
{
  REQUIRE(is_java_generic_parameter(type));
  const java_generic_parametert &generic_param=to_java_generic_parameter(type);
  if(type_variables)
  {
    const java_generic_parametert::type_variablest &generic_type_vars=
      generic_param.type_variables();
    REQUIRE(generic_type_vars.size()==type_variables.value().size());
    REQUIRE(
      std::equal(
        type_variables->begin(),
        type_variables->end(),
        generic_type_vars.begin(),
        [](
          const irep_idt &type_var_name,
          const java_generic_parametert::type_variablet &param)
          {
            REQUIRE(!is_java_generic_inst_parameter((param)));
            return param.get_identifier()==type_var_name;
          }));
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

