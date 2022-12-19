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
    cex_other
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

  // true if the violation happens in the cause loop
  // false if the violation happens after the cause loop
  bool is_violation_in_loop = true;

  // We collect havoced evaluations of havoced variables and their object sizes
  // and pointer offsets.

  // __CPROVER_OBJECT_SIZE
  std::unordered_map<exprt, mp_integer, irep_hash> object_sizes;
  // all the valuation of havoced variables with primitived type.
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
  optionalt<loop_idt> cause_loop_id;
};

/// Verifier that take a goto program as input, and ouptut formatted
/// counterexamples for counterexample-guided-synthesis.
class cegis_verifiert
{
public:
  cegis_verifiert(
    const invariant_mapt &invariant_candidates,
    goto_modelt &goto_model,
    messaget &log)
    : invariant_candidates(invariant_candidates),
      goto_model(goto_model),
      log(log)
  {
  }

  /// Verify `goto_model`. Return an empty `optionalt if there is no violation.
  /// Otherwise, return the formatted counterexample.
  optionalt<cext> verify();

  /// Result counterexample.
  propertiest properties;
  irep_idt first_violation;

protected:
  // Get the options same as using CBMC api without any flag, and
  // preprocess `goto_model`.
  // TODO: replace the checker with CBMC api once it is implemented.
  optionst get_options();

  // Compute the cause loop of `violation`.
  // We say a loop is the cause loop if the violated predicate is dependent
  // upon the write set of the loop.
  optionalt<loop_idt> get_cause_loop_id(
    const goto_tracet &goto_trace,
    const goto_programt::const_targett violation);

  /// Restore transformed functions to original functions.
  void restore_functions();

  // Build counterexample from trace, and store it in `return_cex`.
  cext build_cex(
    const goto_tracet &goto_trace,
    const source_locationt &loop_entry_loc);

  /// Decide whether the target instruction is in the body of the transformed
  /// loop specified by `loop_id`.
  bool is_instruction_in_transfomed_loop(
    const loop_idt &loop_id,
    const goto_functiont &function,
    unsigned location_number_of_target);

  const invariant_mapt &invariant_candidates;
  goto_modelt &goto_model;
  messaget log;

  /// Map from function names to original functions. It is used to
  /// restore functions with annotated loops to original functions.
  std::unordered_map<irep_idt, goto_programt> original_functions;

  /// Map from instrumented instructions for loop contracts to their
  /// original loop numbers. Returned by `code_contractst`
  std::unordered_map<goto_programt::const_targett, unsigned, const_target_hash>
    original_loop_number_map;

  /// Loop havoc instructions instrumneted during applying loop contracts.
  std::unordered_set<goto_programt::const_targett, const_target_hash>
    loop_havoc_set;
};

#endif // CPROVER_GOTO_SYNTHESIZER_CEGIS_VERIFIER_H
