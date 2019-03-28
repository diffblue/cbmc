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
  /// User provided goto location: function name and (maybe) location number;
  /// the structure wraps this option with a parser
  struct entry_goto_locationt
  {
    irep_idt function_name;
    optionalt<unsigned> location_number;

    entry_goto_locationt() = delete;
    explicit entry_goto_locationt(irep_idt function_name)
      : function_name(function_name)
    {
    }
    explicit entry_goto_locationt(
      irep_idt function_name,
      unsigned location_number)
      : function_name(function_name), location_number(location_number)
    {
    }

    /// Returns the first \ref goto_programt::instructiont represented by this
    ///   goto location, i.e. if there is no location number then the first
    ///   instruction, otherwise the one with the right location number
    /// \param instructions: list of instructions to be searched
    /// \return iterator to the right instruction (or `end()`)
    goto_programt::const_targett find_first_corresponding_instruction(
      const goto_programt::instructionst &instructions) const;
  };

  /// Parse a command line option to extract the user specified entry goto
  ///   location
  /// \param cmdl_option: a string of the format <func[:<n>]>
  /// \return correctly constructed entry goto location
  entry_goto_locationt parse_goto_location(const std::string &cmdl_option);

  /// User provided source location: file name and line number; the structure
  /// wraps this option with a parser
  struct entry_source_locationt
  {
    irep_idt file_name;
    unsigned line_number;

    entry_source_locationt() = delete;
    explicit entry_source_locationt(irep_idt file_name, unsigned line_number)
      : file_name(file_name), line_number(line_number)
    {
    }

    /// Returns the first \ref goto_programt::instructiont represented by this
    ///   source location, i.e. one with the same file name and line number
    /// \param instructions: list of instructions to be searched
    /// \return iterator to the right instruction (or `end()`)
    goto_programt::const_targett find_first_corresponding_instruction(
      const goto_programt::instructionst &instructions) const;
  };

  /// Parse a command line option to extract the user specified entry source
  ///   location
  /// \param cmdl_option: a string of the format <file:n>
  /// \return correctly constructed entry source location
  entry_source_locationt parse_source_location(const std::string &cmdl_option);

  /// Wraps the information needed to identify the entry point. Initializes via
  /// either \ref entry_goto_locationt or \ref entry_source_locationt
  struct entry_locationt
  {
    irep_idt function_name;
    goto_programt::const_targett start_instruction;

    entry_locationt() = default;
    explicit entry_locationt(
      irep_idt function_name,
      goto_programt::const_targett start_instruction)
      : function_name(function_name), start_instruction(start_instruction)
    {
    }
  };

  /// Find and return the entry instruction (requested by the user as goto
  ///   location: function name + location number)
  /// \param entry_goto_location: user specified goto location
  /// \param goto_functions: goto functions to be searched for the entry
  ///   instruction
  /// \return the correctly constructed entry location
  entry_locationt initialize_entry_via_goto(
    const entry_goto_locationt &entry_goto_location,
    const goto_functionst &goto_functions);

  /// Find and return the entry instruction (requested by the user as source
  ///   location: file name + line number)
  /// \param entry_source_location: user specified goto location
  /// \param goto_functions: goto functions to be searched for the entry
  ///   instruction
  /// \return the correctly constructed entry location
  entry_locationt initialize_entry_via_source(
    const entry_source_locationt &entry_source_location,
    const goto_functionst &goto_functions);

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

  /// data to initialize the entry function
  entry_locationt entry_location;

  message_handlert &message_handler;
};

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
