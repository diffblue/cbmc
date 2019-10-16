/*******************************************************************\

Module: Symbolic Execution Config

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H
#define CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H

/// Configuration used for a symbolic execution
struct symex_configt final
{
  /// \brief The maximum depth to take the execution to.
  /// Depth is a count of the instructions that have been executed on any
  /// single path.
  unsigned max_depth;

  bool doing_path_exploration;

  bool allow_pointer_unsoundness;

  bool constant_propagation;

  bool self_loops_to_assumptions;

  bool simplify_opt;

  bool unwinding_assertions;

  bool partial_loops;

  mp_integer debug_level;

  /// \brief Should the additional validation checks be run?
  /// If this flag is set the checks for renaming (both level1 and level2) are
  /// executed in the goto_symex_statet (in the assignment method).
  bool run_validation_checks;

  /// \brief Prints out the path that symex is actively taking during execution,
  /// includes diagnostic information about call stack and guard size.
  bool show_symex_steps;

  /// Maximum sizes for which field sensitivity will be applied to array cells
  std::size_t max_field_sensitivity_array_size;

  /// \brief Whether this run of symex is under complexity limits. This
  /// enables certain analyses that otherwise aren't run.
  bool complexity_limits_active;

  /// \brief Construct a symex_configt using options specified in an
  /// \ref optionst
  explicit symex_configt(const optionst &options);
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_CONFIG_H
