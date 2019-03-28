/*******************************************************************\

Module: Decision procedure with incremental solving with contexts

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Decision procedure with incremental solving with contexts

#ifndef CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_CONTEXTS_H
#define CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_CONTEXTS_H

#include "decision_procedure_assumptions.h"

class decision_procedure_contextst : public decision_procedure_assumptionst
{
public:
  /// Push a new context on the stack
  /// This context becomes a child context nested in the current context.
  virtual void push_context() = 0;

  /// Pop the current context
  virtual void pop_context() = 0;

  virtual ~decision_procedure_contextst() = default;
};

#endif // CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_CONTEXTS_H
