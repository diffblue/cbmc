/******************************************************************\

Module: Harness to initialise memory from memory snapshot

Author: Daniel Poetzl

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
#define CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H

#include <list>
#include <string>

#include "goto_harness_generator.h"

#include <goto-programs/goto_model.h>

#include <util/message.h>
#include <util/optional.h>

#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS                              \
  "(memory-snapshot):"                                                         \
  "(initial-location):" // MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS

// clang-format off
#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP                                 \
  "memory snapshot harness generator (--harness-type\n"                        \
  "  initialise-from-memory-snapshot)\n\n"                                     \
  "--memory-snapshot <file>      initialise memory from JSON memory snapshot\n"\
  "--initial-location <func[:<n>]>\n"                                          \
  "                              use given function and location number as "   \
  "entry\n                              point\n"                               \
  // MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP
// clang-format on

/// Generates a harness which first assigns global variables with values from
/// a given memory snapshot and then calls a specified function. The called
/// function is also modified such that it appears to start executing at the
/// given location number on the first invocation.
class memory_snapshot_harness_generatort : public goto_harness_generatort
{
public:
  explicit memory_snapshot_harness_generatort(message_handlert &message_handler)
    : message_handler(message_handler)
  {
  }

  void generate(goto_modelt &goto_model, const irep_idt &harness_function_name)
    override;

protected:
  void handle_option(
    const std::string &option,
    const std::list<std::string> &values) override;

  void validate_options(const goto_modelt &goto_model) override;

  void
  get_memory_snapshot(const std::string &file, symbol_tablet &snapshot) const;

  void add_init_section(goto_modelt &goto_model) const;

  code_blockt add_assignments_to_globals(const symbol_tablet &snapshot) const;

  void add_call_with_nondet_arguments(
    const symbolt &called_function_symbol,
    code_blockt &code) const;

  void insert_harness_function_into_goto_model(
    goto_modelt &goto_model,
    const symbolt &function) const;

  std::string memory_snapshot_file;

  irep_idt entry_function_name;
  optionalt<unsigned> location_number;

  message_handlert &message_handler;
};

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
