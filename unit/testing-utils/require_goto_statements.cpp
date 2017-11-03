/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include "require_goto_statements.h"
#include "catch.hpp"

#include <algorithm>
#include <util/expr_iterator.h>

/// Expand value of a function to include all child codets
/// \param function_value: The value of the function (e.g. got by looking up
///  the function in the symbol table and getting the value)
/// \return: All ID_code statements in the tree rooted at \p function_value
std::vector<codet>
require_goto_statements::get_all_statements(const exprt &function_value)
{
  std::vector<codet> statements;
  for(auto sub_expression_it = function_value.depth_begin();
      sub_expression_it != function_value.depth_end();
      ++sub_expression_it)
  {
    if(sub_expression_it->id() == ID_code)
    {
      statements.push_back(to_code(*sub_expression_it));
    }
  }

  return statements;
}

/// Find assignment statements of the form \p structure_name.\component_name =
/// \param statements: The statements to look through
/// \param structure_name: The name of variable of type struct
/// \param component_name: The name of the component that should be assigned
/// \return: All the assignments to that component.
std::vector<code_assignt>
require_goto_statements::find_struct_component_assignments(
  const std::vector<codet> &statements,
  const irep_idt &structure_name,
  const irep_idt &component_name)
{
  std::vector<code_assignt> component_assignments;

  for(const auto &assignment : statements)
  {
    if(assignment.get_statement() == ID_assign)
    {
      const code_assignt &code_assign = to_code_assign(assignment);

      if(code_assign.lhs().id() == ID_member)
      {
        const auto &member_expr = to_member_expr(code_assign.lhs());
        const auto &symbol = member_expr.symbol();

        if(
          symbol.get_identifier() == structure_name &&
          member_expr.get_component_name() == component_name)
        {
          component_assignments.push_back(code_assign);
        }
      }
    }
  }
  return component_assignments;
}

/// For a given variable name, gets the assignments to it in the provided
/// instructions.
/// \param pointer_name: The name of the variable
/// \param instructions: The instructions to look through
/// \return: A structure that contains the null assignment if found, and a
/// vector of all other assignments
require_goto_statements::pointer_assignment_locationt
require_goto_statements::find_pointer_assignments(
  const irep_idt &pointer_name,
  const std::vector<codet> &instructions)
{
  pointer_assignment_locationt locations;
  for(const codet &statement : instructions)
  {
    if(statement.get_statement() == ID_assign)
    {
      const code_assignt &code_assign = to_code_assign(statement);
      if(
        code_assign.lhs().id() == ID_symbol &&
        to_symbol_expr(code_assign.lhs()).get_identifier() == pointer_name)
      {
        if(
          code_assign.rhs() ==
          null_pointer_exprt(to_pointer_type(code_assign.lhs().type())))
        {
          locations.null_assignment = code_assign;
        }
        else
        {
          locations.non_null_assignments.push_back(code_assign);
        }
      }
    }
  }

  return locations;
}

/// Find the declaration of the specific variable.
/// \param variable_name: The name of the variable.
/// \param entry_point_instructions: The statements to look through
/// \return The declaration statement corresponding to that variable
/// \throws no_decl_found_exceptiont if no declaration of the specific
/// variable is found
const code_declt &require_goto_statements::require_declaration_of_name(
  const irep_idt &variable_name,
  const std::vector<codet> &entry_point_instructions)
{
  for(const auto &statement : entry_point_instructions)
  {
    if(statement.get_statement() == ID_decl)
    {
      const auto &decl_statement = to_code_decl(statement);

      if(decl_statement.get_identifier() == variable_name)
      {
        return decl_statement;
      }
    }
  }
  throw no_decl_found_exceptiont(variable_name.c_str());
}
