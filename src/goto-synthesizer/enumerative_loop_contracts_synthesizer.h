/*******************************************************************\

Module: Enumerative Loop Contracts Synthesizer

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerative Loop Contracts Synthesizer

// NOLINTNEXTLINE(whitespace/line_length)
#ifndef CPROVER_GOTO_SYNTHESIZER_ENUMERATIVE_LOOP_CONTRACTS_SYNTHESIZER_H
// NOLINTNEXTLINE(whitespace/line_length)
#define CPROVER_GOTO_SYNTHESIZER_ENUMERATIVE_LOOP_CONTRACTS_SYNTHESIZER_H

#include "loop_contracts_synthesizer_base.h"

class messaget;
class goto_modelt;

/// Enumerative loop contracts synthesizers.
/// It is designed for `goto_model` containing only checks instrumented by
/// `goto-instrument` with the `--pointer-check` flag.
/// When other checks present, it will just enumerate candidates and check
/// if they are valid.
class enumerative_loop_contracts_synthesizert
  : public loop_contracts_synthesizer_baset
{
public:
  enumerative_loop_contracts_synthesizert(
    const goto_modelt &goto_model,
    messaget &log)
    : loop_contracts_synthesizer_baset(goto_model, log)
  {
  }

  /// This synthesizer guarantees that, with the synthesized loop contracts,
  /// all checks in the annotated GOTO program pass.
  invariant_mapt synthesize_all() override;
  exprt synthesize(loop_idt loop_id) override;

private:
  /// Initialize invariants as true for all unannotated loops.
  void init_candidates();

  invariant_mapt invariant_candiate_map;
};

// NOLINTNEXTLINE(whitespace/line_length)
#endif // CPROVER_GOTO_SYNTHESIZER_ENUMERATIVE_LOOP_CONTRACTS_SYNTHESIZER_H
