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
#  include <unordered_set>
#  include <unordered_map>

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
    // Always observe variables (this alone helps CaDiCaL's heuristics)
    for(unsigned v : xc.vars)
    {
      if(observed.size() <= v)
      {
        observed.resize(v + 1, false);
        actually_observed.resize(v + 1, false);
      }
      observed[v] = true;
    }

    // Only add to Gauss matrix if rank is below cap
    if(gauss.get_rank() >= 3500 || redundant_count > 350)
      return;

    size_t old_rank = gauss.get_rank();
    gauss.add_xor(xc);
    if(gauss.get_rank() <= old_rank)
      ++redundant_count;
    else
      redundant_count = 0;
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
    if(lazy_mode || disabled)
      return;

    callback_count += lits.size();
    for(int lit : lits)
    {
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var < observed.size() && observed[var])
        gauss.assign(var, lit > 0);
    }

    if(callback_count > 100000 && propagation_count < 100)
      disabled = true;
  }

  void notify_new_decision_level() override
  {
    if(!lazy_mode && !disabled)
      level_trail_sizes.push_back(gauss.trail_size());
  }

  void notify_backtrack(size_t new_level) override
  {
    if(!lazy_mode && !disabled)
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

  int cb_decide() override
  {
    // XOR-guided decisions: suggest the unassigned variable appearing
    // in the most Gauss matrix rows. Only every 64th decision to avoid
    // overwhelming CaDiCaL's VSIDS heuristic.
    // Currently disabled — the O(vars) scan per suggestion doesn't
    // justify the marginal benefit. Needs a maintained priority queue.
    return 0;
  }

  int cb_propagate() override
  {
    if(lazy_mode || disabled)
      return 0;

    if(gauss.has_conflict())
      return 0;

    int lit = gauss.propagate();
    while(lit != 0)
    {
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var < observed.size() && observed[var])
      {
        current_propagated = lit;
        stored_reasons[lit] = gauss.get_reason(lit);
        ++propagation_count;
        return lit;
      }
      lit = gauss.propagate();
    }
    return 0;
  }

  int cb_add_reason_clause_lit(int propagated_lit) override
  {
    if(pending_reason.empty())
    {
      auto it = stored_reasons.find(propagated_lit);
      auto raw = (it != stored_reasons.end()) ? it->second : gauss.get_reason(propagated_lit);
      // Deduplicate and filter to observed variables
      std::unordered_set<int> seen;
      for(int lit : raw)
      {
        unsigned var = static_cast<unsigned>(std::abs(lit));
        if(var < observed.size() && observed[var] && seen.insert(lit).second)
          pending_reason.push_back(lit);
      }
      reason_idx = 0;
      if(pending_reason.empty())
        pending_reason.push_back(propagated_lit);
    }
    if(reason_idx < pending_reason.size())
      return pending_reason[reason_idx++];
    pending_reason.clear();
    reason_idx = 0;
    return 0;
  }

  bool cb_has_external_clause(bool &is_forgettable) override
  {
    if(lazy_mode || disabled)
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
  size_t decide_count = 0;
  size_t callback_count = 0;
  size_t propagation_count = 0;
  size_t redundant_count = 0;
  std::unordered_map<int, std::vector<int>> stored_reasons;
  bool disabled = false;

  // Conflict clause state
  std::vector<int> conflict_clause;
  size_t conflict_idx = 0;
};

#endif // HAVE_CADICAL
#endif // CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_H
