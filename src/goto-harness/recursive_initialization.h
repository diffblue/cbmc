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
#include <util/std_types.h>

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

  std::string to_string() const; // for debugging purposes
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
  void initialize_array(
    const exprt &array,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);
  void initialize_dynamic_array(
    const exprt &pointer,
    std::size_t depth,
    const recursion_sett &known_tags,
    code_blockt &body);

  bool should_be_treated_as_array(const irep_idt &pointer_name) const;
  bool is_array_size_parameter(const irep_idt &cmdline_arg) const;
  optionalt<irep_idt>
  get_associated_size_variable(const irep_idt &array_name) const;
};

#endif // CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
