/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
#define CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H

#include <map>

#include <goto-programs/goto_model.h>
#include <util/expr.h>
#include <util/message.h>
#include <util/std_types.h>

struct recursive_initialization_configt
{
  std::size_t min_null_tree_depth = 1;
  std::size_t max_nondet_tree_depth = 2;
  irep_idt mode;
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
};

#endif // CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
