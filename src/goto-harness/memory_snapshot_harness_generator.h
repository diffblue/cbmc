/******************************************************************\

Module: Harness to initialise memory from memory snapshot

Author: Daniel Poetzl

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
#define CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H

#include <list>
#include <string>

#include "goto_harness_generator.h"
#include "recursive_initialization.h"

#include <goto-programs/goto_model.h>

#include <util/message.h>
#include <util/optional.h>

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
  /// \param cmdl_option: a string of the format `name:number`
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
    /// \return <iterator to the right instruction (or `end()`), distance to
    ///   `line_number`>
    std::pair<goto_programt::const_targett, size_t>
    find_first_corresponding_instruction(
      const goto_programt::instructionst &instructions) const;
  };

  /// Parse a command line option to extract the user specified entry source
  ///   location
  /// \param cmdl_option: a string of the format `name:number`
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

  /// Wraps the information for source location match candidates. Keeps track of
  /// the distance between user specified source code line and goto-program
  /// instruction line.
  struct source_location_matcht
  {
    size_t distance;
    irep_idt function_name;
    goto_programt::const_targett instruction;
    bool match_found;

    source_location_matcht() : distance(0), match_found(false)
    {
    }

    void match_up(
      const size_t &candidate_distance,
      const irep_idt &candidate_function_name,
      const goto_programt::const_targett &candidate_instruction)
    {
      if(match_found && distance <= candidate_distance)
        return;

      match_found = true;
      distance = candidate_distance;
      function_name = candidate_function_name;
      instruction = candidate_instruction;
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
  /// \param func_init_done_var: symbol expression for the `func_init_done`
  ///   variable
  /// \param goto_model: Model where the modification takes place
  void add_init_section(
    const symbol_exprt &func_init_done_var,
    goto_modelt &goto_model) const;

  /// Introduce a new symbol into \p symbol_table with the same name and type as
  ///   \p snapshot_symbol
  /// \param snapshot_symbol: the unknown symbol to be introduced
  /// \param symbol_table: the symbol table to be updated
  /// \return the new symbol
  const symbolt &fresh_symbol_copy(
    const symbolt &snapshot_symbol,
    symbol_tablet &symbol_table) const;

  /// For each global symbol in the \p snapshot symbol table either:
  /// 1) add \ref code_assignt assigning a value from the \p snapshot to the
  ///    symbol
  /// or
  /// 2) recursively initialise the symbol to a non-deterministic value of the
  ///    right type.
  /// Malloc(ed) pointers point to temporaries which do not exists in the symbol
  ///   table: for these we introduce fresh symbols.
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

  /// Recursively compute the pointer depth
  /// \param t: input type
  /// \return pointer depth of type \p t
  size_t pointer_depth(const typet &t) const;

  template <typename Adder>
  void collect_references(const exprt &expr, Adder &&add_reference) const
  {
    if(expr.id() == ID_symbol)
      add_reference(to_symbol_expr(expr).get_identifier());
    for(const auto &operand : expr.operands())
    {
      collect_references(operand, add_reference);
    }
  }

  /// Simple structure for linearising posets. Should be constructed with a map
  /// assigning a key to a set of keys that precede it.
  template <typename Key>
  struct preordert
  {
  public:
    using relationt = std::multimap<Key, Key>;
    using keyst = std::set<Key>;

    explicit preordert(const relationt &preorder_relation)
      : preorder_relation(preorder_relation)
    {
    }

    template <typename T>
    void sort(
      const std::vector<std::pair<Key, T>> &input,
      std::vector<std::pair<Key, T>> &output)
    {
      std::unordered_map<Key, T> searchable_input;
      using valuet = std::pair<Key, T>;

      for(const auto &item : input)
      {
        searchable_input[item.first] = item.second;
      }
      auto associate_key_with_t =
        [&searchable_input](const Key &key) -> optionalt<valuet> {
        if(searchable_input.count(key) != 0)
          return valuet(key, searchable_input[key]);
        else
          return {};
      };
      auto push_to_output = [&output](const valuet &value) {
        output.push_back(value);
      };
      for(const auto &item : input)
      {
        dfs(item, associate_key_with_t, push_to_output);
      }
    }

  private:
    const relationt &preorder_relation;

    keyst seen;
    keyst inserted;

    template <typename Value, typename Map, typename Handler>
    void dfs(Value &&node, Map &&key_to_t, Handler &&handle)
    {
      PRECONDITION(seen.empty() && inserted.empty());
      dfs_inner(node, key_to_t, handle);
      seen.clear();
      inserted.clear();
    }

    template <typename Value, typename Map, typename Handler>
    void dfs_inner(Value &&node, Map &&key_to_t, Handler &&handle)
    {
      const Key &key = node.first;
      if(seen.count(key) == 0)
      {
        seen.insert(key);
        auto key_range = preorder_relation.equal_range(key);
        for(auto it = key_range.first; it != key_range.second; ++it)
        {
          auto maybe_value = key_to_t(it->second);
          if(maybe_value.has_value())
            dfs_inner(*maybe_value, key_to_t, handle);
        }
      }
      if(inserted.count(key) != 0)
        return;
      handle(node);
      inserted.insert(key);
    }
  };

  /// data to store the command-line options
  std::string memory_snapshot_file;
  std::string initial_goto_location_line;
  std::string initial_source_location_line;
  std::unordered_set<irep_idt> variables_to_havoc;

  /// data to initialize the entry function
  entry_locationt entry_location;

  message_handlert &message_handler;

  recursive_initialization_configt recursive_initialization_config;
};

#endif // CPROVER_GOTO_HARNESS_MEMORY_SNAPSHOT_HARNESS_GENERATOR_H
