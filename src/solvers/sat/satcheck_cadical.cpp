#include <random>
#include <algorithm>
/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#ifdef HAVE_CADICAL

#  include "satcheck_cadical.h"

#  include "cadical_xor_propagator_simple.h"
// TEMP: using ExtProp
#  include <cadical.hpp>
// Native Gauss: uses solver->add_xor() instead of ExternalPropagator

#  include <util/exception_utils.h>
#  include <util/invariant.h>
#  include <util/narrow.h>
#  include <cstdlib>
#  include <util/threeval.h>

#  include <cadical.hpp>

tvt satcheck_cadical_baset::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  unsigned v = a.var_no();
  if(renumber_variables && !var_map.empty() && v < var_map.size())
    v = var_map[v];

  if(v > narrow<unsigned>(solver->vars()))
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val = solver->val(static_cast<int>(v), true);
  if(val>0)
    result = tvt(!a.sign());
  else if(val<0)
    result = tvt(a.sign());
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  return result;
}

std::string satcheck_cadical_baset::solver_text() const
{
  return std::string("CaDiCaL ") + solver->version();
}

void satcheck_cadical_baset::lcnf(const bvt &bv)
{
  for(const auto &lit : bv)
  {
    if(lit.is_true())
      return;
    else if(!lit.is_false())
      INVARIANT(lit.var_no() < no_variables(), "reject out of bound variables");
  }

  if(renumber_variables)
  {
    // Buffer clause as flat sequence terminated by 0
    for(const auto &lit : bv)
    {
      if(!lit.is_false())
        clause_buffer.push_back(lit.dimacs());
    }
    clause_buffer.push_back(0);
  }
  else
  {
    for(const auto &lit : bv)
    {
      if(!lit.is_false())
        solver->add(lit.dimacs());
    }
    solver->add(0);
  }

  if(solver_hardness)
  {
    // To map clauses to lines of program code, track clause indices in the
    // dimacs cnf output. Dimacs output is generated after processing
    // clauses to remove duplicates and clauses that are trivially true.
    // Here, a clause is checked to see if it can be thus eliminated. If
    // not, add the clause index to list of clauses in
    // solver_hardnesst::register_clause().
    static size_t cnf_clause_index = 0;
    bvt cnf;
    bool clause_removed = process_clause(bv, cnf);

    if(!clause_removed)
      cnf_clause_index++;

    solver_hardness->register_clause(
      bv, cnf, cnf_clause_index, !clause_removed);
  }

  clause_counter++;
}

propt::resultt satcheck_cadical_baset::do_prop_solve(const bvt &assumptions)
{
  INVARIANT(status != statust::ERROR, "there cannot be an error");

  // Flush buffered clauses with remapped variable IDs
  if(renumber_variables && !clause_buffer.empty())
  {
    build_variable_map();
    const unsigned map_size = static_cast<unsigned>(var_map.size());
    // Move buffer to local and free member memory before CaDiCaL allocates
    std::vector<int> buf = std::move(clause_buffer);
    clause_buffer.clear();
    clause_buffer.shrink_to_fit();
    for(int lit : buf)
    {
      if(lit == 0)
      {
        solver->add(0);
      }
      else
      {
        unsigned v = static_cast<unsigned>(lit > 0 ? lit : -lit);
        int mapped =
          (v < map_size) ? static_cast<int>(var_map[v]) : static_cast<int>(v);
        solver->add(lit > 0 ? mapped : -mapped);
      }
    }
  }


  log.statistics() << (no_variables() - 1) << " variables, " << clause_counter
                   << " clauses" << messaget::eom;

  // Add priority decisions for control variables
  for(const auto &lit : control_variables)
  {
    int d = lit.dimacs();
    if(renumber_variables && !var_map.empty())
    {
      unsigned v = lit.var_no();
      if(v < var_map.size())
        d = lit.sign() ? -static_cast<int>(var_map[v])
                       : static_cast<int>(var_map[v]);
    }
    solver->decide_first(d > 0 ? d : -d);
  }

  // if assumptions contains false, we need this to be UNSAT
  for(const auto &a : assumptions)
  {
    if(a.is_false())
    {
      log.status() << "got FALSE as assumption: instance is UNSATISFIABLE"
                   << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }
  }

  for(const auto &a : assumptions)
    if(!a.is_true())
    {
      int d = a.dimacs();
      solver->assume(renumber_variables ? remap_dimacs(d) : d);
    }

  // set preprocessing and inprocessing limits
  auto limit1_ret = solver->limit("preprocessing", preprocessing_limit);
  CHECK_RETURN(limit1_ret);
  auto limit2_ret = solver->limit("localsearch", localsearch_limit);
  CHECK_RETURN(limit2_ret);

  // Connect XOR Gaussian elimination propagator if we have XOR constraints
  // and the feature is enabled via --xor-gauss (or CBMC_XOR_GAUSS env var).
  if(!pending_xors.empty() &&
     (std::getenv("CBMC_XOR_GAUSS") || xor_gauss_enabled))
  {
    // Hybrid: native Gauss for fast propagation, ExternalPropagator for reasons
    // Using native CaDiCaL Gauss propagator
    for(auto &xc : pending_xors)
    {
      if(renumber_variables && !var_map.empty())
      {
        for(auto &v : xc.vars)
        {
          if(v < var_map.size() && var_map[v] != 0)
            v = var_map[v];
        }
      }
      // Add to native Gauss (for fast propagation)
      std::vector<int> dimacs_lits;
      for(unsigned v : xc.vars)
        dimacs_lits.push_back(static_cast<int>(v));
      solver->add_xor(dimacs_lits, xc.rhs);
    }
    // Perform Gaussian elimination and extract derived clauses
    auto derived = solver->gauss_eliminate();
    size_t n_unit = 0, n_binary = 0, n_ternary = 0;
    for(auto &dc : derived)
    {
      for(int lit : dc.lits)
        solver->add(lit);
      solver->add(0);
      if(dc.lits.size() == 0) {} else if(dc.lits.size() == 1)
        n_unit++;
      else if(dc.lits.size() == 2)
        n_binary++;
      else if(dc.lits.size() == 3)
        n_ternary++;
    }

    log.statistics() << "XOR Gauss: " << pending_xors.size()
                     << " XOR constraints -> " << n_unit << " unit, "
                     << n_binary << " binary, " << n_ternary << " ternary derived clauses"
                     << messaget::eom;
    pending_xors.clear();
  }

  switch(solver->solve())
  {
  case 10:
    log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
    status = statust::SAT;
    return resultt::P_SATISFIABLE;
  case 20:
    log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
    break;
  default:
    log.status() << "SAT checker: solving returned without solution"
                 << messaget::eom;
    throw analysis_exceptiont(
      "solving inside CaDiCaL SAT solver has been interrupted");
  }

  status = statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

void satcheck_cadical_baset::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

#  if 0
/// Generate a new variable and return it as a literal
/// \return New variable as literal
literalt satcheck_cadical_baset::new_variable()
{
  int new_var_index = solver->declare_more_variables(1);
  CHECK_RETURN(new_var_index >= 0);
  set_no_variables(new_var_index + 1);
  return literalt{static_cast<literalt::var_not>(new_var_index), false};
}

/// Generate a vector of new variables.
/// \return Vector of new variables.
bvt satcheck_cadical_baset::new_variables(std::size_t width)
{
  bvt result;
  result.reserve(width);

  for(std::size_t i = _no_variables; i < _no_variables + width; ++i)
    result.emplace_back(i, false);

  int new_max_var_index = solver->declare_more_variables(width);
  CHECK_RETURN(new_max_var_index >= 0);
  set_no_variables(new_max_var_index + 1);

  return result;
}
#  endif

satcheck_cadical_baset::satcheck_cadical_baset(
  int _preprocessing_limit,
  int _localsearch_limit,
  message_handlert &message_handler)
  : cnf_solvert(message_handler),
    solver(new CaDiCaL::Solver()),
    preprocessing_limit(_preprocessing_limit),
    localsearch_limit(_localsearch_limit)
{
  solver->set("quiet", 1);
  // Explicitly disable bounded variable addition as initial experiments suggest
  // that this results in degraded performance. If we ever choose to enable it
  // then the above overrides of `new_variable` and `new_variables` need to be
  // enabled.
  solver->set("factor", 0);
  // Pass through CaDiCaL options from environment
  if(const char *opts = std::getenv("CADICAL_OPTS")) {
    std::string s(opts);
    size_t pos = 0;
    while(pos < s.size()) {
      size_t eq = s.find('=', pos);
      size_t comma = s.find(',', pos);
      if(eq != std::string::npos && (comma == std::string::npos || eq < comma)) {
        std::string key = s.substr(pos, eq - pos);
        size_t end = (comma != std::string::npos) ? comma : s.size();
        int val = std::stoi(s.substr(eq + 1, end - eq - 1));
        solver->set(key.c_str(), val);
        pos = (comma != std::string::npos) ? comma + 1 : s.size();
      } else break;
    }
  }
  // Phase will be set via set_phase() before solving
}

satcheck_cadical_baset::~satcheck_cadical_baset()
{
  if(xor_propagator)
    solver->disconnect_external_propagator();
  delete solver;
}

void satcheck_cadical_baset::set_phase(int p)
{
  initial_phase = p;
  solver->set("phase", p);
}

void satcheck_cadical_baset::enable_xor_gauss()
{
  xor_gauss_enabled = true;
}

void satcheck_cadical_baset::add_xor_constraint(
  const std::vector<literalt> &lits,
  bool rhs)
{
  xor_constraintt xc;
  xc.rhs = rhs;
  for(const auto &lit : lits)
  {
    if(lit.is_constant())
    {
      if(lit.is_true())
        xc.rhs = !xc.rhs;
      continue;
    }
    // Use DIMACS variable number (1-based)
    xc.vars.push_back(lit.var_no());
    if(lit.sign())
      xc.rhs = !xc.rhs;
  }
  if(!xc.vars.empty() && pending_xors.size() < xor_constraint_limit)
    pending_xors.push_back(std::move(xc));
}

bool satcheck_cadical_baset::is_in_conflict(literalt a) const
{
  int d = a.dimacs();
  return solver->failed(renumber_variables ? remap_dimacs(d) : d);
}

void satcheck_cadical_baset::build_variable_map()
{
  unsigned n = narrow<unsigned>(no_variables());

  // Only build the map once; extend for new variables
  if(!var_map.empty())
  {
    // Map already built. Assign IDs to any new variables.
    unsigned old_n = narrow<unsigned>(var_map.size());
    if(n > old_n)
    {
      unsigned next_id = old_n; // continue from where we left off
      // Find actual max ID used
      for(unsigned v = 1; v < old_n; ++v)
        if(var_map[v] > next_id) next_id = var_map[v];
      next_id++;
      var_map.resize(n, 0);
      for(unsigned v = old_n; v < n; ++v)
        var_map[v] = next_id++;
    }
    return;
  }

  var_map.resize(n, 0);

  unsigned next_id = 1;
  unsigned num_aux = 0;

  if(reorder_strategy == 0)
  {
    // Strategy 0: aux first (creation order), input last
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(!is_input) { var_map[v] = next_id++; ++num_aux; }
    }
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(is_input) var_map[v] = next_id++;
    }
  }
  else if(reorder_strategy == 1)
  {
    // Strategy 1: aux REVERSE order first (late-created aux = low ID),
    // then input variables
    for(unsigned v = n - 1; v >= 1; --v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(!is_input) { var_map[v] = next_id++; ++num_aux; }
    }
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(is_input) var_map[v] = next_id++;
    }
  }
  else if(reorder_strategy == 2)
  {
    // Strategy 2: input first, aux last
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(is_input) { var_map[v] = next_id++; }
    }
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(!is_input) { var_map[v] = next_id++; ++num_aux; }
    }
  }
  else if(reorder_strategy == 3)
  {
    // Strategy 3: input first, aux REVERSE last
    for(unsigned v = 1; v < n; ++v)
    {
      bool is_input = v < input_variables.size() && input_variables[v];
      if(is_input) var_map[v] = next_id++;
    }
  }
  else if(reorder_strategy == 4)
  {
    // Strategy 4: random permutation (for debugging)
    std::vector<unsigned> ids;
    for(unsigned i = 1; i < n; ++i)
      ids.push_back(i);
    std::mt19937 rng(42);
    std::shuffle(ids.begin(), ids.end(), rng);
    for(unsigned v = 1; v < n; ++v)
    {
      var_map[v] = ids[v - 1];
      bool is_input = v < input_variables.size() && input_variables[v];
      if(!is_input) ++num_aux;
    }
  }

  log.statistics() << "Variable renumbering (strategy " << reorder_strategy
                   << "): " << num_aux << " aux, "
                   << (n - 1 - num_aux) << " input" << messaget::eom;
}

int satcheck_cadical_baset::remap_dimacs(int dimacs_lit) const
{
  unsigned v = static_cast<unsigned>(std::abs(dimacs_lit));
  if(v < var_map.size() && var_map[v] != 0)
  {
    int mapped = static_cast<int>(var_map[v]);
    return dimacs_lit > 0 ? mapped : -mapped;
  }
  return dimacs_lit;
}

#endif
