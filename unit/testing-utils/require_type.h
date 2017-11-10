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

const symbol_typet &
require_symbol(const typet &type, const irep_idt &identifier = "");

struct_typet::componentt require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name);

code_typet require_code(const typet &type);

code_typet::parametert
require_parameter(const code_typet &function_type, const irep_idt &param_name);

code_typet require_code(const typet &type, const size_t num_params);

// A mini DSL for describing an expected set of type parameters for a
// java_generic_typet
enum class type_parameter_kindt
{
  Inst,
  Var
};
struct expected_type_parametert
{
  type_parameter_kindt kind;
  irep_idt description;
};
typedef std::initializer_list<expected_type_parametert>
  expected_type_parameterst;

java_generic_typet require_java_generic_type(const typet &type);

java_generic_typet require_java_generic_type(
  const typet &type,
  const require_type::expected_type_parameterst &type_expectations);

java_generic_parametert require_java_generic_parameter(const typet &type);

java_generic_parametert require_java_generic_parameter(
  const typet &type,
  const require_type::expected_type_parametert &type_expectation);

const typet &require_java_non_generic_type(
  const typet &type,
  const optionalt<symbol_typet> &expect_subtype);

java_generic_class_typet require_java_generic_class(const typet &class_type);

java_generic_class_typet require_java_generic_class(
  const typet &class_type,
  const std::initializer_list<irep_idt> &type_variables);

java_class_typet require_java_non_generic_class(const typet &class_type);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_TYPE_H
