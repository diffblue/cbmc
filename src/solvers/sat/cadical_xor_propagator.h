/// \file
/// CaDiCaL external propagator that performs Gaussian elimination
/// over XOR constraints extracted from the adder encoding.

#ifndef CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_H
#define CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_H

#ifdef HAVE_CADICAL

#  include "xor_gauss.h"

#  include <cadical.hpp>

#  include <cstdlib>
#  include <vector>

/// Bridges xor_gausst to CaDiCaL's ExternalPropagator interface.
class cadical_xor_propagatort : public CaDiCaL::ExternalPropagator
{
public:
  explicit cadical_xor_propagatort(CaDiCaL::Solver *_solver)
    : solver(_solver)
  {
    is_lazy = false;
    are_reasons_forgettable = true;
  }

  /// Add a XOR constraint and observe its variables.
  /// Must be called before solving.
  void add_xor(const xor_constraintt &xc)
  {
    gauss.add_xor(xc);
    for(unsigned v : xc.vars)
    {
      if(observed.size() <= v)
      {
        observed.resize(v + 1, false);
        actually_observed.resize(v + 1, false);
      }
      if(!observed[v])
        observed[v] = true;
    }
  }

  /// Connect to solver and register observed variables.
  /// Must be called after connect_external_propagator.
  void finalize_observations()
  {
    // Always observe all variables — the callbacks are no-ops in lazy mode
    observe_all_vars();
  }

  void observe_all_vars()
  {
    for(unsigned v = 0; v < observed.size(); ++v)
    {
      if(observed[v] && !actually_observed[v])
      {
        solver->add_observed_var(static_cast<int>(v));
        actually_observed[v] = true;
      }
    }
  }

  size_t num_xors() const
  {
    return gauss.num_xors();
  }

  /// Enable/disable lazy mode. In lazy mode, the propagator observes
  /// assignments but doesn't propagate until activated.
  void set_lazy(bool lazy)
  {
    lazy_mode = lazy;
    conflict_count = 0;
  }

  // --- ExternalPropagator interface ---

  void notify_assignment(const std::vector<int> &lits) override
  {
    if(lazy_mode)
      return; // Don't even track assignments until activated

    for(int lit : lits)
    {
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var < observed.size() && observed[var])
        gauss.assign(var, lit > 0);
    }
  }

  void notify_new_decision_level() override
  {
    if(!lazy_mode)
      level_trail_sizes.push_back(gauss.trail_size());
  }

  void notify_backtrack(size_t new_level) override
  {
    if(!lazy_mode)
    {
      if(new_level < level_trail_sizes.size())
      {
        size_t target = level_trail_sizes[new_level];
        gauss.backtrack(target);
        level_trail_sizes.resize(new_level);
      }
      pending_reason.clear();
      current_propagated = 0;
    }
    // Count backtracks as proxy for conflicts
    if(lazy_mode)
    {
      conflict_count++;
      if(conflict_count >= 100)
      {
        lazy_mode = false;
        observe_all_vars();
      }
    }
  }

  bool cb_check_found_model(const std::vector<int> &) override
  {
    return true; // XOR constraints are also in CNF, so model is valid
  }

  int cb_propagate() override
  {
    if(lazy_mode)
      return 0; // Don't propagate until activated

    if(gauss.has_conflict())
      return 0;

    int lit = gauss.propagate();
    if(lit != 0)
      current_propagated = lit;
    return lit;
  }

  int cb_add_reason_clause_lit(int propagated_lit) override
  {
    if(pending_reason.empty())
    {
      pending_reason = gauss.get_reason(propagated_lit);
      reason_idx = 0;
    }
    if(reason_idx < pending_reason.size())
      return pending_reason[reason_idx++];
    pending_reason.clear();
    reason_idx = 0;
    return 0; // clause terminator
  }

  bool cb_has_external_clause(bool &is_forgettable) override
  {
    if(lazy_mode)
      return false;
    is_forgettable = true;
    return gauss.has_conflict();
  }

  int cb_add_external_clause_lit() override
  {
    if(conflict_clause.empty())
      conflict_clause = gauss.get_conflict_clause();
    if(conflict_idx < conflict_clause.size())
      return conflict_clause[conflict_idx++];
    conflict_clause.clear();
    conflict_idx = 0;
    return 0;
  }

private:
  CaDiCaL::Solver *solver;
  xor_gausst gauss;
  std::vector<bool> observed;
  std::vector<bool> actually_observed;
  std::vector<size_t> level_trail_sizes;

  // Reason clause state
  std::vector<int> pending_reason;
  size_t reason_idx = 0;
  int current_propagated = 0;

  // Lazy activation
  bool lazy_mode = false;
  size_t conflict_count = 0;

  // Conflict clause state
  std::vector<int> conflict_clause;
  size_t conflict_idx = 0;
};

#endif // HAVE_CADICAL
#endif // CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_H
