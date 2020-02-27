/*******************************************************************\

Module: Capability to collect the statistics of the complexity of individual
        solver queries.

Author: diffblue

\*******************************************************************/

/// \file
/// Capability to collect the statistics of the complexity of individual solver
/// queries.

#ifndef CPROVER_SOLVERS_HARDNESS_COLLECTOR_H
#define CPROVER_SOLVERS_HARDNESS_COLLECTOR_H

#include <solvers/solver_hardness.h>

class exprt;

class hardness_collectort
{
public:
  virtual bool is_hardness_collection_enabled() const
  {
    return false;
  }
  virtual void enable_hardness_collection()
  {
  }
  virtual solver_hardnesst &get_solver_hardness() = 0;

  virtual ~hardness_collectort() = default;
};

#endif // CPROVER_SOLVERS_HARDNESS_COLLECTOR_H
