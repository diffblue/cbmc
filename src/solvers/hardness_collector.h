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

#include <solvers/prop/literal.h>

#include <memory>

struct solver_hardnesst;

class clause_hardness_collectort
{
public:
  /// Called e.g. from the `satcheck_minisat2::lcnf`, this function adds the
  ///   complexity statistics from the last SAT query to the `current_ssa_key`.
  /// \param bv: the clause (vector of literals)
  /// \param cnf: processed clause
  /// \param cnf_clause_index: index of clause in dimacs output
  /// \param register_cnf: negation of boolean variable tracking if the clause
  /// can be eliminated
  virtual void register_clause(
    const bvt &bv,
    const bvt &cnf,
    const size_t cnf_clause_index,
    bool register_cnf) = 0;

  virtual ~clause_hardness_collectort()
  {
  }
};

class hardness_collectort
{
public:
  std::unique_ptr<clause_hardness_collectort> solver_hardness;
};

#endif // CPROVER_SOLVERS_HARDNESS_COLLECTOR_H
