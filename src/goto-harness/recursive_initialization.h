/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
#define CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H

#include <map>
#include <set>

#include <goto-programs/goto_model.h>
#include <util/expr.h>
#include <util/message.h>
#include <util/optional.h>
#include <util/prefix.h>
#include <util/std_types.h>

#include "function_harness_generator_options.h"
#include "goto_harness_generator.h"

struct recursive_initialization_configt
{
  std::size_t min_null_tree_depth = 1;
  std::size_t max_nondet_tree_depth = 2;
  irep_idt mode;

  // array stuff
  std::size_t max_dynamic_array_size = 2;
  std::size_t min_dynamic_array_size = 1;

  std::set<irep_idt> pointers_to_treat_as_arrays;
  std::set<irep_idt> variables_that_hold_array_sizes;
  std::map<irep_idt, irep_idt> array_name_to_associated_array_size_variable;

  std::set<irep_idt> pointers_to_treat_as_cstrings;

  std::string to_string() const; // for debugging purposes

  /// Parse the options specific for recursive initialisation
  /// \param option: the user option name
  /// \param values: the (one-or-more) values for this option
  /// \return true if the option belonged to recursive initialisation and was
  ///   successfully parsed here
  bool handle_option(
    const std::string &option,
    const std::list<std::string> &values);
};

/// Class for generating initialisation code
/// for compound structures.
class recursive_initializationt
{
public:
  using recursion_sett = std::set<irep_idt>;

  recursive_initializationt(
    recursive_initialization_configt initialization_config,
    goto_modelt &goto_model);

  /// Generate initialisation code for lhs into body.
  /// \param lhs: The expression to initialise.
  /// \param depth: The number of pointer follows. Starts at 0.
  /// \param known_tags: The struct tags we've already seen during recursion.
  /// \param body: The code block to write initialisation code to.
  void initialize(
    const exprt &lhs,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);

  /// Get the `free` function as symbol expression, and inserts it into the
  ///   goto-model if it doesn't exist already.
  /// \return the symbol expression for the `free` function
  symbol_exprt get_free_function();

  bool is_initialization_allowed(const symbolt &symbol)
  {
    return (
      symbol.is_static_lifetime && symbol.is_lvalue &&
      symbol.type.id() != ID_code &&
      !has_prefix(id2string(symbol.name), CPROVER_PREFIX));
  }

private:
  const recursive_initialization_configt initialization_config;
  goto_modelt &goto_model;

  /// Get the malloc function as symbol exprt,
  /// and inserts it into the goto-model if it doesn't
  /// exist already.
  symbol_exprt get_malloc_function();

  void initialize_struct_tag(
    const exprt &lhs,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);
  void initialize_pointer(
    const exprt &lhs,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);
  void initialize_nondet(
    const exprt &lhs,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);

  using array_convertert = std::function<void(
    const exprt &pointer,
    std::size_t length,
    std::size_t current_index,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body)>;
  array_convertert default_array_member_initialization();
  array_convertert cstring_member_initialization();

  void initialize_array(
    const exprt &array,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body,
    array_convertert array_member_initialization);
  void initialize_dynamic_array(
    const exprt &pointer,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body,
    array_convertert array_member_initialization);

  void initialize_cstring(
    const exprt &pointer,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);

  bool should_be_treated_as_array(const irep_idt &pointer_name) const;
  bool is_array_size_parameter(const irep_idt &cmdline_arg) const;
  optionalt<irep_idt>
  get_associated_size_variable(const irep_idt &array_name) const;
  bool should_be_treated_as_cstring(const irep_idt &pointer_name) const;

  /// Construct a new global symbol of type `int` and set it's value to \p
  ///   initial_value.
  /// \param symbol_name: the base name for the new symbol
  /// \param initial_value: the value the symbol should be initialised with
  /// \return unique name assigned to the new symbol (may differ from \p
  ///   symbol_name)
  irep_idt get_fresh_global_name(
    const std::string &symbol_name,
    const exprt &initial_value) const;

  /// Construct a new global symbol of type `int` initialised to 0.
  /// \param symbol_name: the base name for the new symbol
  /// \return the symbol expression associated with the new symbol
  symbol_exprt get_fresh_global_symexpr(const std::string &symbol_name) const;

  /// Construct a new local symbol of type `int` initialised to 0.
  /// \param symbol_name: the base name for the new symbol
  /// \return the symbol expression associated with the new symbol
  symbol_exprt get_fresh_local_symexpr(const std::string &symbol_name) const;

  /// Construct a new local symbol of type \p type initialised to \p init_value.
  /// \param symbol_name: the base name for the new symbol
  /// \param type: type for the new symbol
  /// \param init_value: expression the symbol should be initialised with
  /// \return the symbol expression associated with the new symbol
  symbol_exprt get_fresh_local_typed_symexpr(
    const std::string &symbol_name,
    const typet &type,
    const exprt &init_value) const;

  /// Construct a new function symbol of type \p fun_type.
  /// \param fun_name: the base name for the new symbol
  /// \param fun_type: type for the new symbol
  /// \return the new symbol
  const symbolt &
  get_fresh_fun_symbol(const std::string &fun_name, const typet &fun_type);

  /// Construct a new parameter symbol of type \p param_type.
  /// \param param_name: the base name for the new parameter
  /// \param param_type: type for the new symbol
  /// \return the new symbol
  symbolt &get_fresh_param_symbol(
    const std::string &param_name,
    const typet &param_type);

  /// Recover the symbol expression from symbol table.
  /// \param symbol_name: the name of the symbol to get
  /// \return symbol expression of the symbol with given name
  symbol_exprt get_symbol_expr(const irep_idt &symbol_name) const;

  /// Simple pretty-printer for \ref typet. Produces strings that can decorate
  ///   variable names in C.
  /// \param type: type to be pretty-printed
  /// \return a string without white characters, quotes, etc.
  std::string type2id(const typet &type) const;
};

#endif // CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
