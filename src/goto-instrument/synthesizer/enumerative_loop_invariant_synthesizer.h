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

#include <goto-programs/goto_model.h>

#include "loop_invariant_synthesizer_base.h"

class messaget;

/// Enumerative loop invariant synthesizers.
/// It handles `goto_model` containing only checks instrumented by
/// `goto-instrument` with the `--pointer-check` flag.
class enumerative_loop_invariant_synthesizert
  : public loop_invariant_synthesizer_baset
{
public:
  enumerative_loop_invariant_synthesizert(
    const goto_modelt &goto_model,
    messaget &log)
    : loop_invariant_synthesizer_baset(goto_model, log)
  {
  }

  invariant_mapt synthesize_all() override;
  exprt synthesize(loop_idt loop_id) override;

private:
  /// Initialize invariants as true for all unannotated loops.
  void init_candidates();

  invariant_mapt invariant_candiate_map;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_ENUMERATIVE_LOOP_INVARIANT_SYNTHESIZER_H
