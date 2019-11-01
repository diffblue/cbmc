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
  using type_constructor_namest = std::map<typet, irep_idt>;

  recursive_initializationt(
    recursive_initialization_configt initialization_config,
    goto_modelt &goto_model);

  /// Generate initialisation code for lhs into body.
  /// \param lhs: The expression to initialise.
  /// \param depth: The number of pointer follows. Starts at 0.
  /// \param body: The code block to write initialisation code to.
  void initialize(const exprt &lhs, const exprt &depth, code_blockt &body);

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
  irep_idt max_depth_var_name;
  irep_idt min_depth_var_name;
  type_constructor_namest type_constructor_names;

  /// Get the malloc function as symbol exprt,
  /// and inserts it into the goto-model if it doesn't
  /// exist already.
  symbol_exprt get_malloc_function();

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

  /// Case analysis for which constructor should be used.
  /// \param depth_symbol: the symbol for `depth` parameter
  /// \param result_symbol: the symbol for `result` parameter
  /// \param size_symbol: maybe the symbol for `size` parameter
  /// \param lhs_name: the name of the original symbol
  /// \return the body of the constructor
  code_blockt build_constructor_body(
    const exprt &depth_symbol,
    const exprt &result_symbol,
    const optionalt<exprt> &size_symbol,
    const optionalt<irep_idt> &lhs_name);

  /// Check if a constructor for the type of \p expr already exists and create
  ///   it if not.
  /// \param expr: the expression to be constructed
  /// \return name of the constructor function
  const irep_idt &build_constructor(const exprt &expr);

  /// Generic constructor for all pointers: only builds one pointee (not an
  ///   array) but may recourse in case the pointee contains more pointers, e.g.
  ///   a struct.
  /// \param depth: symbol of the depth parameter
  /// \param result: symbol of the result parameter
  /// \return the body of the constructor
  code_blockt
  build_pointer_constructor(const exprt &depth, const exprt &result);

  /// Constructor for structures: simply iterates over members and initialise
  ///   each one.
  /// \param depth: symbol of the depth parameter
  /// \param result: symbol of the result parameter
  /// \return the body of the constructor
  code_blockt build_struct_constructor(const exprt &depth, const exprt &result);

  /// Default constructor: assigns non-deterministic value of the right type.
  /// \param result: symbol of the result parameter
  /// \return the body of the constructor
  code_blockt build_nondet_constructor(const exprt &result) const;

  /// Constructor for arrays: simply iterates over elements and initialise
  ///   each one.
  /// \param depth: symbol of the depth parameter
  /// \param result: symbol of the result parameter
  /// \return the body of the constructor
  code_blockt build_array_constructor(const exprt &depth, const exprt &result);

  /// Constructor for dynamic arrays: allocate memory for `n` elements (`n` is
  ///   random but bounded) and initialise each one.
  /// \param depth: symbol of the depth parameter
  /// \param result: symbol of the result parameter
  /// \param size: symbol of the size parameter
  /// \param lhs_name: name of the original symbol
  /// \return the body of the constructor
  code_blockt build_dynamic_array_constructor(
    const exprt &depth,
    const exprt &result,
    const exprt &size,
    const optionalt<irep_idt> &lhs_name);

  /// Constructor for strings: as array but the last element is zero.
  /// \param result: symbol of the result parameter
  /// \return the body of the constructor
  code_blockt build_array_string_constructor(const exprt &result) const;
};

#endif // CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
