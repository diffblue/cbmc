/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Utilties for inspecting goto functions

#include <goto-programs/goto_instruction_code.h>

#include <util/optional.h>

#include <regex>

class symbol_tablet;

#ifndef CPROVER_JAVA_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H
#define CPROVER_JAVA_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H

// NOLINTNEXTLINE(readability/namespace)
namespace require_goto_statements
{
struct pointer_assignment_locationt
{
  optionalt<code_assignt> null_assignment;
  std::vector<code_assignt> non_null_assignments;
};

class no_decl_found_exceptiont : public std::exception
{
public:
  explicit no_decl_found_exceptiont(const std::string &var_name)
    : message{"Failed to find declaration for: " + var_name}
  {
  }

  virtual const char *what() const throw()
  {
    return message.c_str();
  }

private:
  std::string message;
};

pointer_assignment_locationt find_struct_component_assignments(
  const std::vector<codet> &statements,
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &component_name,
  const symbol_tablet &symbol_table);

pointer_assignment_locationt find_this_component_assignment(
  const std::vector<codet> &statements,
  const irep_idt &component_name);

std::vector<codet> get_all_statements(const exprt &function_value);

const std::vector<codet>
require_entry_point_statements(const symbol_tablet &symbol_table);

pointer_assignment_locationt find_pointer_assignments(
  const irep_idt &pointer_name,
  const std::vector<codet> &instructions);

pointer_assignment_locationt find_pointer_assignments(
  const std::regex &pointer_name_match,
  const std::vector<codet> &instructions);

const code_declt &require_declaration_of_name(
  const irep_idt &variable_name,
  const std::vector<codet> &entry_point_instructions);

const irep_idt &require_struct_component_assignment(
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &component_name,
  const irep_idt &component_type_name,
  const optionalt<irep_idt> &typecast_name,
  const std::vector<codet> &entry_point_instructions,
  const symbol_tablet &symbol_table);

const irep_idt &require_struct_array_component_assignment(
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &array_component_name,
  const irep_idt &array_type_name,
  const std::vector<codet> &entry_point_instructions,
  const symbol_tablet &symbol_table);

const irep_idt &require_entry_point_argument_assignment(
  const irep_idt &argument_name,
  const std::vector<codet> &entry_point_statements);

std::vector<code_function_callt> find_function_calls(
  const std::vector<codet> &statements,
  const irep_idt &function_call_identifier);
}

#endif // CPROVER_JAVA_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H
