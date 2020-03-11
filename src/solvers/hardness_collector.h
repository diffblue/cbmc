/*******************************************************************\

Module: Capability to collect the statistics of the complexity of individual
        solver queries.

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Capability to collect the statistics of the complexity of individual solver
/// queries.

#ifndef CPROVER_SOLVERS_HARDNESS_COLLECTOR_H
#define CPROVER_SOLVERS_HARDNESS_COLLECTOR_H

#include <functional>
#include <solvers/solver_hardness.h>

class exprt;

class hardness_collectort
{
public:
  using handlert = std::function<void(solver_hardnesst &)>;
  virtual void with_solver_hardness(handlert handler) = 0;
  virtual void enable_hardness_collection() = 0;
  virtual ~hardness_collectort() = default;
};

template <typename T>
void with_solver_hardness(
  T &maybe_hardness_collector,
  hardness_collectort::handlert handler)
{
  // FIXME I am wondering if there is a way to do this that is a bit less
  // dynamically typed.
  if(
    auto hardness_collector =
      dynamic_cast<hardness_collectort *>(&maybe_hardness_collector))
  {
    hardness_collector->with_solver_hardness(handler);
  }
}
#endif // CPROVER_SOLVERS_HARDNESS_COLLECTOR_H
