/*******************************************************************\

Module: Loop Contracts Synthesizer Interface

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Loop Contracts Synthesizer Interface

#ifndef CPROVER_GOTO_SYNTHESIZER_LOOP_CONTRACTS_SYNTHESIZER_BASE_H
#define CPROVER_GOTO_SYNTHESIZER_LOOP_CONTRACTS_SYNTHESIZER_BASE_H

#include <goto-programs/goto_model.h>

#include "synthesizer_utils.h"

class messaget;

/// A base class for loop contracts synthesizers.
/// Provides a method for synthesizing loop contracts in a given `goto_model`.
///
/// Derived class should clarify what types of `goto_model` they targets, e.g.,
/// a `goto_model` contains only memory safety checks, or a `goto_model`
/// contains both memory safety checks and correctness checks.
class loop_contracts_synthesizer_baset
{
public:
  loop_contracts_synthesizer_baset(goto_modelt &goto_model, messaget &log)
    : goto_model(goto_model), log(log)
  {
  }
  virtual ~loop_contracts_synthesizer_baset() = default;

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

#endif // CPROVER_GOTO_SYNTHESIZER_LOOP_CONTRACTS_SYNTHESIZER_BASE_H
