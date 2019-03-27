/*******************************************************************\

Module: Decision procedure with incremental solving

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Decision procedure with incremental solving

#ifndef CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_INCREMENTAL_H
#define CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_INCREMENTAL_H

#include "decision_procedure.h"
#include "literal.h"

class decision_procedure_incrementalt : public decision_proceduret
{
public:
  /// Prevent the solver-level variable associated with literal \p a from being
  /// optimized away by the decision procedure
  virtual void set_frozen(literalt a) = 0;

  /// Prevent the solver-level variables in the given bitvector \p bv from being
  /// optimized away by the decision procedure
  virtual void set_frozen(const bvt &bv);

  /// Prevent all solver-level variables encoding symbols occurring in the
  /// expressions passed to the decision procedure from being optimized away
  virtual void set_all_frozen() = 0;

  virtual ~decision_procedure_incrementalt() = default;
};

#endif // CPROVER_SOLVERS_PROP_DECISION_PROCEDURE_INCREMENTAL_H
