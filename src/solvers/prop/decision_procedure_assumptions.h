/*******************************************************************\

Module: Decision procedure with incremental solving under assumptions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Decision procedure with incremental solving under assumptions

#ifndef CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_ASSUMPTIONS_H
#define CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_ASSUMPTIONS_H

#include "decision_procedure_incremental.h"

class decision_procedure_assumptionst : public decision_procedure_incrementalt
{
public:
  /// Set assumptions for the next call to operator() to solve the problem
  virtual void set_assumptions(const bvt &) = 0;

  virtual ~decision_procedure_assumptionst() = default;
};

#endif // CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_ASSUMPTIONS_H
