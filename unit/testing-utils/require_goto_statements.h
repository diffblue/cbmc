/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Utilties for inspecting goto functions

#include <util/irep.h>
#include <util/expr.h>
#include <util/optional.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <goto-programs/goto_program.h>

#ifndef CPROVER_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H
#define CPROVER_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H

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
    : _varname(var_name)
  {
  }

  virtual const char *what() const throw()
  {
    std::ostringstream stringStream;
    stringStream << "Failed to find declaration for: " << _varname;
    return stringStream.str().c_str();
  }

private:
  std::string _varname;
};

std::vector<code_assignt> find_struct_component_assignments(
  const std::vector<codet> &statements,
  const irep_idt &structure_name,
  const irep_idt &component_name);

std::vector<codet> get_all_statements(const exprt &function_value);

pointer_assignment_locationt find_pointer_assignments(
  const irep_idt &pointer_name,
  const std::vector<codet> &instructions);

const code_declt &require_declaration_of_name(
  const irep_idt &variable_name,
  const std::vector<codet> &entry_point_instructions);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_GOTO_STATEMENTS_H
