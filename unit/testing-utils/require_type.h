/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific types
/// If the type is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#ifndef CPROVER_TESTING_UTILS_REQUIRE_TYPE_H
#define CPROVER_TESTING_UTILS_REQUIRE_TYPE_H

#include <util/optional.h>
#include <util/std_types.h>
#include <java_bytecode/java_types.h>


// NOLINTNEXTLINE(readability/namespace)
namespace require_type
{
pointer_typet
require_pointer(const typet &type, const optionalt<typet> &subtype);

struct_typet::componentt require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name);

code_typet require_code(const typet &type);

code_typet::parametert
require_parameter(const code_typet &function_type, const irep_idt &param_name);

code_typet require_code(
  const typet &type,
  const size_t num_params);

const java_generic_typet &require_java_generic_type_variables(
  const typet &type,
  const optionalt<std::initializer_list<irep_idt>> &type_variables);

const java_generic_typet &require_java_generic_type_instantiations(
  const typet &type,
  const optionalt<std::initializer_list<irep_idt>> &type_instantiations);

const java_generic_parametert &require_java_generic_parameter_variables(
  const typet &type,
  const optionalt<irep_idt> &type_variables);

const typet &require_java_non_generic_type(
  const typet &type,
  const optionalt<irep_idt> &expect_type);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_TYPE_H
