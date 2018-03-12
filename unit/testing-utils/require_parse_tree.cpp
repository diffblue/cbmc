/*******************************************************************\

 Module: Unit test utilities

 Author: Diffblue Ltd.

\*******************************************************************/

#include "require_parse_tree.h"

/// Find in the parsed class a specific entry within the
/// lambda_method_handle_map with a matching descriptor. Will fail if no
/// matching lambda entry found.
/// \param parsed_class: the class to inspect
/// \param descriptor: the descriptor the lambda method should have
/// \param entry_index: the number to skip (i.e. if multiple entries with the
/// same descriptor
/// \return
require_parse_tree::lambda_method_handlet
require_parse_tree::require_lambda_entry_for_descriptor(
  const java_bytecode_parse_treet::classt &parsed_class,
  const std::string &descriptor,
  const size_t entry_index)
{
  REQUIRE(entry_index < parsed_class.lambda_method_handle_map.size());
  typedef java_bytecode_parse_treet::classt::lambda_method_handle_mapt::
    value_type lambda_method_entryt;

  size_t matches_found = 0;

  const auto matching_lambda_entry = std::find_if(
    parsed_class.lambda_method_handle_map.begin(),
    parsed_class.lambda_method_handle_map.end(),
    [&descriptor, &matches_found, &entry_index](
      const lambda_method_entryt &entry) {
      if(entry.second.method_type == descriptor)
      {
        ++matches_found;
        return matches_found == entry_index + 1;
      }
      return false;
    });

  INFO("Looking for descriptor: " << descriptor);
  std::ostringstream found_entries;
  for(const auto entry : parsed_class.lambda_method_handle_map)
  {
    found_entries << id2string(entry.first.first) << ": "
                  << id2string(entry.second.method_type) << std::endl;
  }
  INFO("Found descriptors:\n" << found_entries.str());

  REQUIRE(matching_lambda_entry != parsed_class.lambda_method_handle_map.end());

  return matching_lambda_entry->second;
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
