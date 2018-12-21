/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

#include "require_parse_tree.h"

#include <iterator>

/// Find in the parsed class a specific entry within the
/// lambda_method_handle_map with a matching descriptor. Will fail if no
/// matching lambda entry found.
/// \param parsed_class the class to inspect
/// \param lambda_method_ref the reference/descriptor of the lambda method
///   to which this lambda entry points to, must be unique
/// \param method_type the descriptor the lambda method should have
/// \return
require_parse_tree::lambda_method_handlet
require_parse_tree::require_lambda_entry_for_descriptor(
  const java_bytecode_parse_treet::classt &parsed_class,
  const std::string &lambda_method_ref,
  const std::string &method_type)
{
  typedef java_bytecode_parse_treet::classt::lambda_method_handle_mapt::
    value_type lambda_method_entryt;

  INFO(
    "Looking for entry with lambda_method_ref: " << lambda_method_ref
                                                 << " and method_type: "
                                                 << method_type);
  std::vector<lambda_method_entryt> matches;
  std::copy_if(
    parsed_class.lambda_method_handle_map.begin(),
    parsed_class.lambda_method_handle_map.end(),
    back_inserter(matches),
    [&method_type,
     &lambda_method_ref](const lambda_method_entryt &entry) { //NOLINT
      return (
        entry.second.method_type == method_type &&
        entry.second.lambda_method_ref == lambda_method_ref);
    });
  REQUIRE(matches.size() == 1);
  return matches.at(0).second;
}

/// Finds a specific method in the parsed class with a matching name.
/// \param parsed_class: The class
/// \param method_name: The name of the method to look for
/// \return The methodt structure with the corresponding name
const require_parse_tree::methodt require_parse_tree::require_method(
  const java_bytecode_parse_treet::classt &parsed_class,
  const irep_idt &method_name)
{
  const auto method = std::find_if(
    parsed_class.methods.begin(),
    parsed_class.methods.end(),
    [&method_name](const java_bytecode_parse_treet::methodt &method) {
      return method.name == method_name;
    });

  INFO("Looking for method: " << method_name);
  std::ostringstream found_methods;
  for(const auto entry : parsed_class.methods)
  {
    found_methods << id2string(entry.name) << std::endl;
  }
  INFO("Found methods:\n" << found_methods.str());

  REQUIRE(method != parsed_class.methods.end());

  return *method;
}

/// Verify whether a given methods instructions match an expectation
/// \param expected_instructions: The expected instructions for a given method
/// \param instructions: The instructions of a method
void require_parse_tree::require_instructions_match_expectation(
  const expected_instructionst &expected_instructions,
  const java_bytecode_parse_treet::methodt::instructionst instructions)
{
  REQUIRE(instructions.size() == expected_instructions.size());
  auto actual_instruction_it = instructions.begin();
  for(const auto expected_instruction : expected_instructions)
  {
    expected_instruction.require_instructions_equal(*actual_instruction_it);
    ++actual_instruction_it;
  }
}

/// Check whether a given instruction matches an expectation of the instruction
/// \param actual_instruction: The instruction to check
void require_parse_tree::expected_instructiont::require_instructions_equal(
  java_bytecode_parse_treet::instructiont actual_instruction) const
{
  REQUIRE(actual_instruction.statement == instruction_mnemoic);
  REQUIRE(actual_instruction.args.size() == instruction_arguments.size());
  auto actual_arg_it = actual_instruction.args.begin();
  for(const exprt &expected_arg : actual_instruction.args)
  {
    INFO("Expected argument" << expected_arg.pretty());
    INFO("Actual argument" << actual_arg_it->pretty());
    REQUIRE(*actual_arg_it == expected_arg);
    ++actual_arg_it;
  }
}
