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

// clang-format off
#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS                              \
  "(memory-snapshot):"                                                         \
  "(initial-goto-location):"                                                   \
  "(initial-source-location):"                                                 \
  "(havoc-variables):" // MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS
// clang-format on

// clang-format off
#define MEMORY_SNAPSHOT_HARNESS_GENERATOR_HELP                                 \
  "memory snapshot harness generator (--harness-type\n"                        \
  "  initialise-from-memory-snapshot)\n\n"                                     \
  "--memory-snapshot <file>      initialise memory from JSON memory snapshot\n"\
  "--initial-goto-location <func[:<n>]>\n"                                     \
  "                              use given function and location number as "   \
  "entry\n                              point\n"                               \
  "--initial-source-location <file:n>\n"                                       \
  "                              use given file and line as entry point\n"     \
  "--havoc-variables vars        initialise variables from vars to\n"          \
  "                              non-deterministic values"                     \
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

  /// The main function of this harness, consists of the following:
  /// 1. Load memory table from the snapshot.
  /// 2. Add initial section to the user-specified initial location.
  /// 3. Assign global variables their snapshot values (via the harness
  ///    function).
  /// 4. Insert call of the initial location (with nondet values) into the
  ///    harness function.
  /// 5. Build symbol for the harness functions.
  /// 6. Insert harness function into \p goto_model.
  /// \param goto_model: goto model to be modified
  /// \param harness_function_name: name of the resulting harness function
  void generate(goto_modelt &goto_model, const irep_idt &harness_function_name)
    override;

protected:
  /// Collect the memory-snapshot specific cmdline options (one at a time)
  /// \param option: memory-snapshot | initial-location | havoc-variables
  /// \param values: list of arguments related to a given option
  void handle_option(
    const std::string &option,
    const std::list<std::string> &values) override;

  /// Check that user options make sense:
  /// On their own, e.g. location number cannot be specified without a function.
  /// In relation to the input program, e.g. function name must be known via
  ///   the symbol table.
  /// \param goto_model: the model containing the symbol table, goto functions,
  ///   etc.
  void validate_options(const goto_modelt &goto_model) override;

  /// Parse the snapshot JSON file and initialise the symbol table
  /// \param file: the snapshot JSON file
  /// \param snapshot: the resulting symbol table built from the snapshot
  void
  get_memory_snapshot(const std::string &file, symbol_tablet &snapshot) const;

  /// Modify the entry-point function to start from the user-specified initial
  ///   location.
  /// Turn this:
  ///
  ///    int foo() {
  ///      ..first_part..
  /// i:   //location_number=i
  ///      ..second_part..
  ///    }
  ///
  /// Into this:
  ///
  ///   func_init_done;
  ///   __CPROVER_initialize() {
  ///     ...
  ///     func_init_done = false;
  ///   }
  ///   int foo() {
  ///     if (func_init_done) goto 1;
  ///     func_init_done = true;
  ///     goto i;
  /// 1:  ;
  ///     ..first_part..
  /// i:  //location_number=i
  ///     ..second_part..
  ///   }
  ///
  /// \param goto_model: Model where the modification takes place
  void add_init_section(goto_modelt &goto_model) const;

  /// For each global symbol in the \p snapshot symbol table either:
  /// 1) add \ref code_assignt assigning a value from the \p snapshot to the
  ///    symbol
  /// or
  /// 2) recursively initialise the symbol to a non-deterministic value of the
  ///    right type
  /// \param snapshot: snapshot to load the symbols and their values from
  /// \param goto_model: model to initialise the havoc-ing
  /// \return the block of code where the assignments are added
  code_blockt add_assignments_to_globals(
    const symbol_tablet &snapshot,
    goto_modelt &goto_model) const;

  /// Create as many non-deterministic arguments as there are arguments of the
  /// \p called_function_symbol and add a function call with those arguments
  /// \param called_function_symbol: the function to be called
  /// \param code: the block of code where the function call is added
  void add_call_with_nondet_arguments(
    const symbolt &called_function_symbol,
    code_blockt &code) const;

  /// Insert the \p function into the symbol table (and the goto functions map)
  /// of the \p goto_model
  /// \param goto_model: goto model where the insertion is to take place
  /// \param function: symbol of the function to be inserted
  void insert_harness_function_into_goto_model(
    goto_modelt &goto_model,
    const symbolt &function) const;

  std::string memory_snapshot_file;

  irep_idt entry_function_name;
  optionalt<unsigned> location_number;
  std::unordered_set<irep_idt> variables_to_havoc;

  message_handlert &message_handler;
};

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
