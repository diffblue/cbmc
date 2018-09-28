/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Helper functions for requiring specific types
/// If the type is of the wrong type, throw a CATCH exception
/// Also checks associated properties and returns a casted version of the
/// expression.

#ifndef CPROVER_JAVA_TESTING_UTILS_REQUIRE_TYPE_H
#define CPROVER_JAVA_TESTING_UTILS_REQUIRE_TYPE_H

#include <util/optional.h>
#include <util/std_types.h>
#include <java_bytecode/java_types.h>

// NOLINTNEXTLINE(readability/namespace)
namespace require_type
{
pointer_typet
require_pointer(const typet &type, const optionalt<typet> &subtype);

const struct_tag_typet &
require_struct_tag(const typet &type, const irep_idt &identifier = "");

struct_typet::componentt require_component(
  const struct_typet &struct_type,
  const irep_idt &component_name);

code_typet require_code(const typet &type);
java_method_typet require_java_method(const typet &type);

code_typet::parametert
require_parameter(const code_typet &function_type, const irep_idt &param_name);

code_typet require_code(const typet &type, const size_t num_params);
java_method_typet
require_java_method(const typet &type, const size_t num_params);

// A mini DSL for describing an expected set of type arguments for a
// java_generic_typet
enum class type_argument_kindt
{
  Inst,
  Var
};
struct expected_type_argumentt
{
  type_argument_kindt kind;
  irep_idt description;
};
typedef std::initializer_list<expected_type_argumentt>
  expected_type_argumentst;

java_generic_typet require_java_generic_type(const typet &type);

java_generic_typet require_java_generic_type(
  const typet &type,
  const require_type::expected_type_argumentst &type_expectations);

java_generic_parametert require_java_generic_parameter(const typet &type);

java_generic_parametert require_java_generic_parameter(
  const typet &type,
  const irep_idt &parameter);

const typet &require_java_non_generic_type(
  const typet &type,
  const optionalt<struct_tag_typet> &expect_subtype);

class_typet require_complete_class(const typet &class_type);

class_typet require_incomplete_class(const typet &class_type);

java_generic_class_typet require_java_generic_class(const typet &class_type);

java_generic_class_typet require_java_generic_class(
  const typet &class_type,
  const std::initializer_list<irep_idt> &type_variables);

java_generic_class_typet
require_complete_java_generic_class(const typet &class_type);

java_generic_class_typet require_complete_java_generic_class(
  const typet &class_type,
  const std::initializer_list<irep_idt> &type_parameters);

java_implicitly_generic_class_typet
require_java_implicitly_generic_class(const typet &class_type);

java_implicitly_generic_class_typet require_java_implicitly_generic_class(
  const typet &class_type,
  const std::initializer_list<irep_idt> &implicit_type_variables);

java_implicitly_generic_class_typet
require_complete_java_implicitly_generic_class(const typet &class_type);

java_implicitly_generic_class_typet
require_complete_java_implicitly_generic_class(
  const typet &class_type,
  const std::initializer_list<irep_idt> &implicit_type_variables);

java_class_typet require_java_non_generic_class(const typet &class_type);

java_class_typet
require_complete_java_non_generic_class(const typet &class_type);

java_generic_struct_tag_typet require_java_generic_struct_tag_type(
  const typet &type,
  const std::string &identifier);

java_generic_struct_tag_typet require_java_generic_struct_tag_type(
  const typet &type,
  const std::string &identifier,
  const require_type::expected_type_argumentst &type_expectations);

typedef java_class_typet::java_lambda_method_handlest
  java_lambda_method_handlest;

java_lambda_method_handlest require_lambda_method_handles(
  const java_class_typet &class_type,
  const std::vector<std::string> &expected_identifiers);
}

#endif // CPROVER_JAVA_TESTING_UTILS_REQUIRE_TYPE_H
