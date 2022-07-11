/*******************************************************************\

Module: Loop Invariant Synthesizer Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Loop Invariant Synthesizer Interface

#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H

#include <util/message.h>

#include <goto-programs/goto_model.h>

#include "synthesizer_utils.h"

#define OPT_SYNTHESIZE_LOOP_INVARIANTS "(synthesize-loop-invariants)"
#define HELP_LOOP_INVARIANT_SYNTHESIZER                                        \
  " --synthesize-loop-invariants\n"                                            \
  "                              synthesize and apply loop invariants\n"

class loop_invariant_synthesizer_baset
{
public:
  loop_invariant_synthesizer_baset(goto_modelt &goto_model, messaget &log)
    : goto_model(goto_model), log(log)
  {
  }
  virtual ~loop_invariant_synthesizer_baset() = default;

  /// Synthesize loop invariants with which all checks in `goto_model`
  /// succeed. The result is a map from `loop_idt` ids of loops to `exprt`
  /// the goto-expression representation of synthesized invariants.
  virtual invariant_mapt synthesize() = 0;

protected:
  goto_modelt &goto_model;
  messaget &log;
};

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

  invariant_mapt synthesize() override;

private:
  /// Initialize invariants as true for all unannotated loops.
  void init_candidates();

  invariant_mapt invariant_candiate_map{invariant_mapt()};
};

#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_H
