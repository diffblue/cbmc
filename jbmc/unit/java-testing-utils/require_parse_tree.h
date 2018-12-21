/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Utilties for inspecting java_parse_treet

#ifndef CPROVER_JAVA_TESTING_UTILS_REQUIRE_PARSE_TREE_H
#define CPROVER_JAVA_TESTING_UTILS_REQUIRE_PARSE_TREE_H

#include <java_bytecode/java_bytecode_parse_tree.h>

#include <testing-utils/catch.hpp>

// NOLINTNEXTLINE(readability/namespace)
namespace require_parse_tree
{
typedef java_bytecode_parse_treet::classt::lambda_method_handlet
  lambda_method_handlet;

lambda_method_handlet require_lambda_entry_for_descriptor(
  const java_bytecode_parse_treet::classt &parsed_class,
  const std::string &lambda_method_ref,
  const std::string &method_type);

typedef java_bytecode_parse_treet::methodt methodt;

const methodt require_method(
  const java_bytecode_parse_treet::classt &parsed_class,
  const irep_idt &method_name);

struct expected_instructiont
{
  expected_instructiont(
    const irep_idt &instruction_mnemoic,
    const std::vector<exprt> &instruction_arguments)
    : instruction_mnemoic(instruction_mnemoic),
      instruction_arguments(instruction_arguments)
  {
  }

  void require_instructions_equal(
    java_bytecode_parse_treet::instructiont actual_instruction) const;

private:
  irep_idt instruction_mnemoic;
  std::vector<exprt> instruction_arguments;
};

typedef std::vector<expected_instructiont> expected_instructionst;

void require_instructions_match_expectation(
  const expected_instructionst &expected_instructions,
  const java_bytecode_parse_treet::methodt::instructionst instructions);
}

#endif // CPROVER_JAVA_TESTING_UTILS_REQUIRE_PARSE_TREE_H
