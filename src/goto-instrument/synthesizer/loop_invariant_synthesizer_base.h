/*******************************************************************\

Module: Loop Invariant Synthesizer Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Loop Invariant Synthesizer Interface

#ifndef CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_BASE_H
#define CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_BASE_H

#include <goto-programs/goto_model.h>

#include "synthesizer_utils.h"

#define FLAG_SYNTHESIZE_LOOP_INVARIANTS "synthesize-loop-invariants"
#define OPT_SYNTHESIZE_LOOP_INVARIANTS "(" FLAG_SYNTHESIZE_LOOP_INVARIANTS ")"
#define HELP_LOOP_INVARIANT_SYNTHESIZER                                        \
  " --synthesize-loop-invariants\n"                                            \
  "                              synthesize and apply loop invariants\n"

class messaget;

/// A base class for loop invariant synthesizers.
/// Provides a method for synthesizing loop invariants in a given `goto_model`.
///
/// Derived class should clarify what types of `goto_model` they targets, e.g.,
/// a `goto_model` contains only memory safety checks, or a `goto_model`
/// contains both memory safety checks and correctness checks.
class loop_invariant_synthesizer_baset
{
public:
  loop_invariant_synthesizer_baset(goto_modelt &goto_model, messaget &log)
    : goto_model(goto_model), log(log)
  {
  }
  virtual ~loop_invariant_synthesizer_baset() = default;

  /// Synthesize loop invariants that are inductive in the given GOTO program.
  ///
  /// The result is a map from `loop_idt` ids of loops to `exprt`
  /// the GOTO-expression representation of synthesized invariants.
  virtual invariant_mapt synthesize_all() = 0;

  /// Synthesize loop invariant for a specified loop in the `goto_model`.
  virtual exprt synthesize(loop_idt) = 0;

protected:
  goto_modelt &goto_model;
  messaget &log;
};

#endif // CPROVER_GOTO_INSTRUMENT_SYNTHESIZER_LOOP_INVARIANT_SYNTHESIZER_BASE_H
