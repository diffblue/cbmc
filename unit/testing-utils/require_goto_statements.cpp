/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Ltd.

\*******************************************************************/

#include "require_goto_statements.h"
#include "catch.hpp"

#include <algorithm>
#include <util/expr_iterator.h>
#include <goto-programs/goto_functions.h>
#include <java_bytecode/java_types.h>

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

/// \param symbol_table Symbol table for the test
/// \return All codet statements of the __CPROVER_start function
const std::vector<codet>
require_goto_statements::require_entry_point_statements(
  const symbol_tablet &symbol_table)
{
  // Retrieve __CPROVER_start
  const symbolt *entry_point_function =
    symbol_table.lookup(goto_functionst::entry_point());
  REQUIRE(entry_point_function != nullptr);
  return get_all_statements(entry_point_function->value);
}

/// Find assignment statements of the form:
/// - \p structure_name
/// .@\p superclass_name.\p component_name = (if it's a component inherited
/// from the superclass)
/// - \p structure_name.\p component_name = (otherwise)
/// \param statements: The statements to look through
/// \param structure_name: The name of variable of type struct
/// \param superclass_name: The name of the superclass (if given)
/// \param component_name: The name of the component of the superclass that
/// should be assigned
/// \return: All the assignments to that component.
require_goto_statements::pointer_assignment_locationt
require_goto_statements::find_struct_component_assignments(
  const std::vector<codet> &statements,
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &component_name)
{
  pointer_assignment_locationt locations;

  for(const auto &assignment : statements)
  {
    if(assignment.get_statement() == ID_assign)
    {
      const code_assignt &code_assign = to_code_assign(assignment);

      if(code_assign.lhs().id() == ID_member)
      {
        const member_exprt &member_expr = to_member_expr(code_assign.lhs());

        if(superclass_name.has_value())
        {
          // Structure of the expression:
          // member_exprt member_expr:
          // - component name: \p component_name
          // - operand (component of): member_exprt superclass_expr:
          //     - component name: @\p superclass_name
          //     - operand (component of): symbol for \p structure_name
          if(
            member_expr.get_component_name() == component_name &&
            member_expr.compound().id() == ID_member)
          {
            const member_exprt &superclass_expr =
              to_member_expr(member_expr.op0());
            const irep_idt supercomponent_name =
              "@" + id2string(superclass_name.value());

            if(
              superclass_expr.get_component_name() == supercomponent_name &&
              superclass_expr.symbol().get_identifier() == structure_name)
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
        else
        {
          // Structure of the expression:
          // member_exprt member_expr:
          // - component name: \p component_name
          // - operand (component of): symbol for \p structure_name
          if(
            member_expr.op().id() == ID_symbol &&
            member_expr.symbol().get_identifier() == structure_name &&
            member_expr.get_component_name() == component_name)
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
    }
  }
  return locations;
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

/// Checks that the component of the structure (possibly inherited from
/// the superclass) is assigned an object of the given type.
/// \param structure_name The name the variable
/// \param superclass_name The name of its superclass (if given)
/// \param component_name The name of the field of the superclass
/// \param component_type_name The name of the required type of the field
/// \param typecast_name The name of the type to which the object is cast (if
/// there is a typecast)
/// \param entry_point_instructions The statements to look through
/// \return The identifier of the variable assigned to the field
const irep_idt &require_goto_statements::require_struct_component_assignment(
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &component_name,
  const irep_idt &component_type_name,
  const optionalt<irep_idt> &typecast_name,
  const std::vector<codet> &entry_point_instructions)
{
  // First we need to find the assignments to the component belonging to
  // the structure_name object
  const auto &component_assignments =
    require_goto_statements::find_struct_component_assignments(
      entry_point_instructions,
      structure_name,
      superclass_name,
      component_name);
  REQUIRE(component_assignments.non_null_assignments.size() == 1);

  // We are expecting that the resulting statement can be of two forms:
  // 1. structure_name.(@superclass_name if given).component =
  //     (struct cast_type_name *) tmp_object_factory$1;
  //   followed by a direct assignment like this:
  //     tmp_object_factory$1 = &tmp_object_factory$2;
  // 2. structure_name.component = &tmp_object_factory$1;
  exprt component_assignment_rhs_expr =
    component_assignments.non_null_assignments[0].rhs();

  // If the rhs is a typecast (case 1 above), deconstruct it to get the name of
  // the variable and find the assignment to it
  if(component_assignment_rhs_expr.id() == ID_typecast)
  {
    const auto &component_assignment_rhs =
      to_typecast_expr(component_assignment_rhs_expr);

    // Check the type we are casting to
    if(typecast_name.has_value())
    {
      REQUIRE(component_assignment_rhs.type().id() == ID_pointer);
      REQUIRE(
        to_symbol_type(
          to_pointer_type(component_assignment_rhs.type()).subtype())
          .get(ID_identifier) == typecast_name.value());
    }

    const auto &component_reference_tmp_name =
      to_symbol_expr(component_assignment_rhs.op()).get_identifier();
    const auto &component_reference_assignments =
      require_goto_statements::find_pointer_assignments(
        component_reference_tmp_name, entry_point_instructions)
        .non_null_assignments;
    REQUIRE(component_reference_assignments.size() == 1);
    component_assignment_rhs_expr = component_reference_assignments[0].rhs();
  }

  // The rhs assigns an address of a variable, get its name
  const auto &component_reference_assignment_rhs =
    to_address_of_expr(component_assignment_rhs_expr);
  const auto &component_tmp_name =
    to_symbol_expr(component_reference_assignment_rhs.op()).get_identifier();

  // After we have found the declaration of the final assignment's
  // right hand side, then we want to identify that the type
  // is the one we expect, e.g.:
  // struct java.lang.Integer { __CPROVER_string @class_identifier;
  // boolean @lock; } tmp_object_factory$2;
  const auto &component_declaration =
    require_goto_statements::require_declaration_of_name(
      component_tmp_name, entry_point_instructions);
  REQUIRE(component_declaration.symbol().type().id() == ID_struct);
  const auto &component_struct =
    to_struct_type(component_declaration.symbol().type());
  REQUIRE(component_struct.get(ID_name) == component_type_name);

  return component_tmp_name;
}

/// Checks that the array component of the structure (possibly inherited from
/// the superclass) is assigned an array with given element type.
/// \param structure_name The name the variable
/// \param superclass_name The name of its superclass (if given)
/// \param array_component_name The name of the array field of the superclass
/// \param array_type_name The type of the array, e.g., java::array[reference]
/// \param array_component_element_type_name The element type of the array
/// \param entry_point_instructions The statements to look through
/// \return The identifier of the variable assigned to the field
const irep_idt &
require_goto_statements::require_struct_array_component_assignment(
  const irep_idt &structure_name,
  const optionalt<irep_idt> &superclass_name,
  const irep_idt &array_component_name,
  const irep_idt &array_type_name,
  const irep_idt &array_component_element_type_name,
  const std::vector<codet> &entry_point_instructions)
{
  // First we need to find the assignments to the component belonging to
  // the structure_name object
  const auto &component_assignments =
    require_goto_statements::find_struct_component_assignments(
      entry_point_instructions,
      structure_name,
      superclass_name,
      array_component_name);
  REQUIRE(component_assignments.non_null_assignments.size() == 1);

  // We are expecting that the resulting statement is of form:
  // structure_name.array_component_name = (struct array_type_name *)
  //    tmp_object_factory$1;
  const exprt &component_assignment_rhs_expr =
    component_assignments.non_null_assignments[0].rhs();

  // The rhs is a typecast, deconstruct it to get the name of the variable
  // and find the assignment to it
  PRECONDITION(component_assignment_rhs_expr.id() == ID_typecast);
  const auto &component_assignment_rhs =
    to_typecast_expr(component_assignment_rhs_expr);
  const auto &component_reference_tmp_name =
    to_symbol_expr(component_assignment_rhs.op()).get_identifier();

  // Check the type we are casting to matches the array type
  REQUIRE(component_assignment_rhs.type().id() == ID_pointer);
  REQUIRE(
    to_symbol_type(to_pointer_type(component_assignment_rhs.type()).subtype())
      .get(ID_identifier) == array_type_name);

  // Get the tmp_object name and find assignments to it, there should be only
  // one that assigns the correct array through side effect
  const auto &component_reference_assignments =
    require_goto_statements::find_pointer_assignments(
      component_reference_tmp_name, entry_point_instructions);
  REQUIRE(component_reference_assignments.non_null_assignments.size() == 1);
  const exprt &component_reference_assignment_rhs_expr =
    component_reference_assignments.non_null_assignments[0].rhs();

  // The rhs is side effect
  PRECONDITION(component_reference_assignment_rhs_expr.id() == ID_side_effect);
  const auto &array_component_reference_assignment_rhs =
    to_side_effect_expr(component_reference_assignment_rhs_expr);

  // The type of the side effect is an array with the correct element type
  PRECONDITION(
    array_component_reference_assignment_rhs.type().id() == ID_pointer);
  const typet &array =
    to_pointer_type(array_component_reference_assignment_rhs.type()).subtype();
  PRECONDITION(is_java_array_tag(array.get(ID_identifier)));
  REQUIRE(array.get(ID_identifier) == array_type_name);

  return component_reference_tmp_name;
}

/// Checks that the input argument (of method under test) with given name is
/// assigned a single non-null object in the entry point function.
/// \param argument_name Name of the input argument of method under test
/// \param entry_point_statements The statements to look through
/// \return The identifier of the variable assigned to the input argument
const irep_idt &
require_goto_statements::require_entry_point_argument_assignment(
  const irep_idt &argument_name,
  const std::vector<codet> &entry_point_statements)
{
  // Trace the creation of the object that is being supplied as the input
  // argument to the function under test
  const pointer_assignment_locationt &argument_assignments =
    find_pointer_assignments(
      id2string(goto_functionst::entry_point()) + "::" +
        id2string(argument_name),
      entry_point_statements);

  // There should be at most one assignment to it
  REQUIRE(argument_assignments.non_null_assignments.size() == 1);

  // The following finds the name of the tmp object that gets assigned
  // to the input argument. There must be one such assignment only,
  // and usually looks like this:
  //   argument_name = &tmp_object_factory$1;
  const auto &argument_assignment =
    argument_assignments.non_null_assignments[0];
  const auto &argument_tmp_name =
    to_symbol_expr(to_address_of_expr(argument_assignment.rhs()).object())
      .get_identifier();
  return argument_tmp_name;
}
