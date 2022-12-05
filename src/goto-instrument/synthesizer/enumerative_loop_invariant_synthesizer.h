/*******************************************************************\

Module: Enumerative Loop Invariant Synthesizer

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerative Loop Invariant Synthesizer

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_ENUMERATIVE_LOOP_INVARIANT_SYNTHESIZER_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_ENUMERATIVE_LOOP_INVARIANT_SYNTHESIZER_H

#include "loop_invariant_synthesizer_base.h"

class messaget;
class goto_modelt;

/// Enumerative loop invariant synthesizers.
/// It is designed for `goto_model` containing only checks instrumented by
/// `goto-instrument` with the `--pointer-check` flag.
/// When other checks present, it will just enumerate candidates and check
/// if they are valid.
class enumerative_loop_invariant_synthesizert
  : public loop_invariant_synthesizer_baset
{
public:
  enumerative_loop_invariant_synthesizert(
    goto_modelt &goto_model,
    messaget &log)
    : loop_invariant_synthesizer_baset(goto_model, log)
  {
  }

  /// This synthesizer guarantees that, with the synthesized loop invariants,
  /// all checks in the annotated GOTO program pass.
  invariant_mapt synthesize_all() override;
  exprt synthesize(loop_idt loop_id) override;

private:
  /// Initialize invariants as true for all unannotated loops.
  void init_candidates();

  /// Scan all ASSIGN instructions to build the map from tmp_post variables
  /// to their original variables.
  void build_tmp_post_map();

  /// Compute the depedent symbols for a loop with invariant-not-preserved
  /// violation which happen after `new_clause` was added.
  std::set<symbol_exprt> compute_dependent_symbols(
    const loop_idt &cause_loop_id,
    const exprt &new_clause,
    const std::set<exprt> &live_vars);

  /// Synthesize range predicate for OOB violation with `violated_predicate`.
  exprt synthesize_range_predicate(const exprt &violated_predicate);

  /// Synthesize same object predicate for null-pointer violation for
  /// `checked_pointer`.
  exprt synthesize_same_object_predicate(const exprt &checked_pointer);

  /// Synthesize strengthening clause for invariant-not-preserved violation.
  exprt synthesize_strengthening_clause(
    const std::vector<exprt> terminal_symbols,
    const loop_idt &cause_loop_id,
    const irep_idt &violation_id);

  ///  Synthesize invariant of form
  ///   (in_inv || !guard) && (!guard -> pos_inv)
  invariant_mapt in_invariant_clause_map;
  invariant_mapt pos_invariant_clause_map;
  invariant_mapt neg_guards;

  /// Map from tmp_post variables to their original variables.
  std::map<exprt, exprt> tmp_post_map;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_ENUMERATIVE_LOOP_INVARIANT_SYNTHESIZER_H
