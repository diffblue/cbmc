/*******************************************************************\

Module: Verifier for Counterexample-Guided Synthesis

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Verifier for Counterexample-Guided Synthesis

#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_CEGIS_VERIFIER_H
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_CEGIS_VERIFIER_H

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
    const std::map<exprt, std::size_t> &object_sizes,
    const std::map<exprt, std::size_t> &havoced_values,
    const std::map<exprt, std::size_t> &havoced_pointer_offsets,
    const std::map<exprt, std::size_t> &loop_entry_values,
    const std::map<exprt, std::size_t> &loop_entry_offsets,
    const std::set<exprt> &live_variables)
    : object_sizes(object_sizes),
      havoced_values(havoced_values),
      havoced_pointer_offsets(havoced_pointer_offsets),
      loop_entry_values(loop_entry_values),
      loop_entry_offsets(loop_entry_offsets),
      live_variables(live_variables)
  {
  }

  cext()
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
  std::map<exprt, std::size_t> object_sizes;
  // all the valuation of havoced variables with primitived type.
  std::map<exprt, std::size_t> havoced_values;
  // __CPROVER_POINTER_OFFSET
  std::map<exprt, std::size_t> havoced_pointer_offsets;

  // We also collect loop-entry evaluations of havoced variables.
  // __CPROVER_loop_entry
  std::map<exprt, std::size_t> loop_entry_values;
  // __CPROVER_POINTER_OFFSET(__CPROVER_loop_entry( ))
  std::map<exprt, std::size_t> loop_entry_offsets;

  // Set of live variables upon loop head.
  std::set<exprt> live_variables;

  violation_typet cex_type;
  loop_idt cause_loop_id;
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

  /// Verify `goto_model`. Return true if there is no violation.
  /// Otherwise, sotre the formatted counterexample in `return_cex`
  bool verify();

  /// Result counterexample.
  cext return_cex;
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
  loop_idt get_cause_loop_id(
    const goto_tracet &goto_trace,
    const goto_programt::const_targett violation);

  /// Restore transformed functions to original functions.
  void restore_functions();

  // Build counterexample from trace, and store it in `return_cex`.
  cext build_cex(
    const goto_tracet &goto_trace,
    const source_locationt &loop_entry_loc);

  const invariant_mapt &invariant_candidates;
  goto_modelt &goto_model;
  messaget log;

  /// Map from function names to original functions. It is used to
  /// restore functions with annotated loops to original functions.
  std::map<irep_idt, goto_programt> original_functions;
};

#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_CEGIS_VERIFIER_H
