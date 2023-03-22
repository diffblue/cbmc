/*******************************************************************\

Module: Verifier for Counterexample-Guided Synthesis

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier for Counterexample-Guided Synthesis

#ifndef CPROVER_GOTO_SYNTHESIZER_CEGIS_VERIFIER_H
#define CPROVER_GOTO_SYNTHESIZER_CEGIS_VERIFIER_H

#include <goto-programs/goto_model.h>
#include <goto-programs/loop_ids.h>

#include <goto-checker/all_properties_verifier.h>

#include "synthesizer_utils.h"

class messaget;

/// Formatted counterexample.
class cext
{
public:
  enum class violation_typet
  {
    cex_out_of_boundary,
    cex_null_pointer,
    cex_not_preserved,
    cex_not_hold_upon_entry,
    cex_assignable,
    cex_other
  };

  enum class violation_locationt
  {
    in_loop,
    after_loop,
    in_condition
  };

  cext(
    const std::unordered_map<exprt, mp_integer, irep_hash> &object_sizes,
    const std::unordered_map<exprt, mp_integer, irep_hash> &havoced_values,
    const std::unordered_map<exprt, mp_integer, irep_hash>
      &havoced_pointer_offsets,
    const std::unordered_map<exprt, mp_integer, irep_hash> &loop_entry_values,
    const std::unordered_map<exprt, mp_integer, irep_hash> &loop_entry_offsets,
    const std::set<exprt> &live_variables)
    : object_sizes(object_sizes),
      havoced_values(havoced_values),
      havoced_pointer_offsets(havoced_pointer_offsets),
      loop_entry_values(loop_entry_values),
      loop_entry_offsets(loop_entry_offsets),
      live_variables(live_variables)
  {
  }

  explicit cext(const violation_typet &violation_type)
    : violation_type(violation_type)
  {
  }

  // pointer that failed the null pointer check
  exprt checked_pointer;
  exprt violated_predicate;

  // Location where the violation happens
  violation_locationt violation_location = violation_locationt::in_loop;

  // We collect havoced evaluations of havoced variables and their object sizes
  // and pointer offsets.

  // __CPROVER_OBJECT_SIZE
  std::unordered_map<exprt, mp_integer, irep_hash> object_sizes;
  // all the valuation of havoced variables with primitive type.
  std::unordered_map<exprt, mp_integer, irep_hash> havoced_values;
  // __CPROVER_POINTER_OFFSET
  std::unordered_map<exprt, mp_integer, irep_hash> havoced_pointer_offsets;

  // We also collect loop-entry evaluations of havoced variables.
  // __CPROVER_loop_entry
  std::unordered_map<exprt, mp_integer, irep_hash> loop_entry_values;
  // __CPROVER_POINTER_OFFSET(__CPROVER_loop_entry( ))
  std::unordered_map<exprt, mp_integer, irep_hash> loop_entry_offsets;

  // Set of live variables upon loop head.
  std::set<exprt> live_variables;

  violation_typet violation_type;
  std::list<loop_idt> cause_loop_ids;
};

/// Verifier that take a goto program as input, and output formatted
/// counterexamples for counterexample-guided-synthesis.
class cegis_verifiert
{
public:
  cegis_verifiert(
    const invariant_mapt &invariant_candidates,
    const std::map<loop_idt, std::set<exprt>> &assigns_map,
    goto_modelt &goto_model,
    const optionst &options,
    messaget &log)
    : invariant_candidates(invariant_candidates),
      assigns_map(assigns_map),
      goto_model(goto_model),
      options(options),
      log(log),
      ns(goto_model.symbol_table)
  {
  }

  /// Verify `goto_model`. Return an empty `optionalt if there is no violation.
  /// Otherwise, return the formatted counterexample.
  optionalt<cext> verify();

  /// Result counterexample.
  propertiest properties;
  irep_idt target_violation_id;

protected:
  // Compute the cause loops of `violation`.
  // We say a loop is the cause loop if the violated predicate is dependent
  // upon the write set of the loop.
  std::list<loop_idt> get_cause_loop_id(
    const goto_tracet &goto_trace,
    const goto_programt::const_targett violation);

  // Compute the cause loops of a assignable-violation.
  // We say a loop is the cause loop if the assignable check is in the loop.
  std::list<loop_idt>
  get_cause_loop_id_for_assigns(const goto_tracet &goto_trace);

  // Extract the violation type from violation description.
  cext::violation_typet extract_violation_type(const std::string &description);

  // Compute the location of the violation.
  cext::violation_locationt get_violation_location(
    const loop_idt &loop_id,
    const goto_functiont &function,
    unsigned location_number_of_target);

  /// Restore transformed functions to original functions.
  void restore_functions();

  // Build counterexample from trace, and store it in `return_cex`.
  cext build_cex(
    const goto_tracet &goto_trace,
    const source_locationt &loop_entry_loc);

  /// Decide whether the target instruction is in the body of the transformed
  /// loop specified by `loop_id`.
  bool is_instruction_in_transformed_loop(
    const loop_idt &loop_id,
    const goto_functiont &function,
    unsigned location_number_of_target);

  /// Decide whether the target instruction is between the loop-havoc and the
  /// evaluation of the loop guard.
  bool is_instruction_in_transformed_loop_condition(
    const loop_idt &loop_id,
    const goto_functiont &function,
    unsigned location_number_of_target);

  /// Preprocess the goto model to prepare for verification.
  void preprocess_goto_model();

  const invariant_mapt &invariant_candidates;
  const std::map<loop_idt, std::set<exprt>> &assigns_map;
  goto_modelt &goto_model;
  const optionst &options;
  messaget log;
  const namespacet ns;

  /// Map from function names to original functions. It is used to
  /// restore functions with annotated loops to original functions.
  std::unordered_map<irep_idt, goto_programt> original_functions;

  /// Map from instrumented instructions for loop contracts to their
  /// original loop numbers. Returned by `code_contractst`
  std::unordered_map<goto_programt::const_targett, unsigned, const_target_hash>
    original_loop_number_map;

  /// Loop havoc instructions instrumented during applying loop contracts.
  std::unordered_set<goto_programt::const_targett, const_target_hash>
    loop_havoc_set;
};

#endif // CPROVER_GOTO_SYNTHESIZER_CEGIS_VERIFIER_H
