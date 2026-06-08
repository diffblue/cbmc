#ifndef CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_SIMPLE_H
#define CPROVER_SOLVERS_SAT_CADICAL_XOR_PROPAGATOR_SIMPLE_H

#include "xor_propagator.h"
#include <cadical.hpp>
#include <unordered_map>

class cadical_xor_propagator_simplet : public CaDiCaL::ExternalPropagator
{
public:
  explicit cadical_xor_propagator_simplet(CaDiCaL::Solver *s) : solver(s) {}

  void add_xor(const xor_constraintt &xc)
  {
    checker.add_xor(xc);
    for(unsigned v : xc.vars)
    {
      if(v >= observed.size())
        observed.resize(v + 1, false);
      observed[v] = true;
    }
  }

  void finalize_observations()
  {
    for(unsigned v = 0; v < observed.size(); ++v)
      if(observed[v])
        solver->add_observed_var(static_cast<int>(v));
  }

  size_t num_xors() const { return checker.num_xors(); }

  void notify_assignment(const std::vector<int> &lits) override
  {
    for(int lit : lits)
    {
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var < observed.size() && observed[var])
      {
        checker.assign(var, lit > 0);
        dirty_vars.push_back(var);
      }
    }
  }

  void notify_new_decision_level() override
  {
    level_sizes.push_back(dirty_vars.size());
  }

  void notify_backtrack(size_t new_level) override
  {
    size_t target =
      (new_level < level_sizes.size()) ? level_sizes[new_level] : 0;
    while(dirty_vars.size() > target)
    {
      checker.unassign(dirty_vars.back());
      dirty_vars.pop_back();
    }
    level_sizes.resize(new_level);
    checker.clear_queue();
  }

  bool cb_check_found_model(const std::vector<int> &) override
  {
    return true;
  }

  int cb_decide() override { return 0; }

  int cb_propagate() override
  {
    int lit = checker.find_propagation();
    if(lit != 0)
    {
      unsigned var = static_cast<unsigned>(std::abs(lit));
      if(var >= observed.size() || !observed[var])
        return 0;
      stored_reasons[lit] = checker.get_reason(lit);
    }
    return lit;
  }

  int cb_add_reason_clause_lit(int propagated_lit) override
  {
    if(current_reason.empty())
    {
      auto it = stored_reasons.find(propagated_lit);
      if(it != stored_reasons.end())
        current_reason = it->second;
      else
        current_reason = {propagated_lit};
      reason_idx = 0;
    }
    if(reason_idx < current_reason.size())
      return current_reason[reason_idx++];
    current_reason.clear();
    reason_idx = 0;
    return 0;
  }

  bool cb_has_external_clause(bool &) override { return false; }
  int cb_add_external_clause_lit() override { return 0; }

private:
  CaDiCaL::Solver *solver;
  xor_checkert checker;
  std::vector<bool> observed;
  std::vector<unsigned> dirty_vars;
  std::vector<size_t> level_sizes;
  std::unordered_map<int, std::vector<int>> stored_reasons;
  std::vector<int> current_reason;
  size_t reason_idx = 0;
};

#endif
