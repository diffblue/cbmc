/// \file
/// SAT solver backend using CryptoMiniSat with native XOR support.

#include "satcheck_cryptominisat.h"

#ifdef HAVE_CRYPTOMINISAT

#include <cryptominisat5/cryptominisat.h>

#include <util/exception_utils.h>
#include <util/invariant.h>

satcheck_cryptominisatt::satcheck_cryptominisatt(message_handlert &msg)
  : cnf_solvert{msg}, solver{new CMSat::SATSolver{}}
{
  solver->set_num_threads(1);
}

satcheck_cryptominisatt::~satcheck_cryptominisatt()
{
  delete solver;
}

std::string satcheck_cryptominisatt::solver_text() const
{
  return "CryptoMiniSat 5";
}

literalt satcheck_cryptominisatt::new_variable()
{
  literalt l = cnf_solvert::new_variable();
  // Ensure CMS has enough variables (0-based)
  unsigned cms_var = l.var_no() - 1;
  while(solver->nVars() <= cms_var)
    solver->new_var();
  return l;
}

bvt satcheck_cryptominisatt::new_variables(std::size_t width)
{
  bvt result;
  result.reserve(width);
  for(std::size_t i = 0; i < width; i++)
    result.push_back(new_variable());
  return result;
}

void satcheck_cryptominisatt::lcnf(const bvt &bv)
{
  std::vector<CMSat::Lit> cms_clause;
  cms_clause.reserve(bv.size());

  for(const auto &lit : bv)
  {
    if(lit.is_true())
      return; // tautology
    if(lit.is_false())
      continue; // skip

    unsigned var = lit.var_no();
    INVARIANT(var > 0, "variable 0 is reserved for constants");

    unsigned cms_var = var - 1;
    while(solver->nVars() <= cms_var)
      solver->new_var();

    cms_clause.emplace_back(cms_var, lit.sign());
  }

  if(cms_clause.empty())
    return; // empty clause after removing false literals

  solver->add_clause(cms_clause);
  clause_counter++;
}

void satcheck_cryptominisatt::register_xor(const bvt &lits, bool rhs)
{
  xor_constraintt xc;
  bool adjusted_rhs = rhs;

  for(const auto &lit : lits)
  {
    if(lit.is_constant())
    {
      if(lit.is_true())
        adjusted_rhs = !adjusted_rhs;
      continue;
    }

    unsigned var = lit.var_no();
    INVARIANT(var > 0, "variable 0 is reserved for constants");
    xc.vars.push_back(var - 1); // 0-based for CMS

    if(lit.sign())
      adjusted_rhs = !adjusted_rhs;
  }

  if(!xc.vars.empty())
  {
    xc.rhs = adjusted_rhs;
    pending_xors.push_back(std::move(xc));
  }
}

void satcheck_cryptominisatt::set_assignment(literalt a, bool value)
{
  // CMS doesn't support pre-set assignments; use unit clauses
  unsigned var = a.var_no();
  INVARIANT(var > 0, "variable 0 is reserved for constants");
  unsigned cms_var = var - 1;
  while(solver->nVars() <= cms_var)
    solver->new_var();

  bool sign = a.sign() ? !value : value;
  std::vector<CMSat::Lit> unit = {CMSat::Lit{cms_var, !sign}};
  solver->add_clause(unit);
}

satcheck_cryptominisatt::resultt
satcheck_cryptominisatt::do_prop_solve(const bvt &assumptions)
{
  // Add XOR constraints before first solve
  if(!xors_added)
  {
    for(auto &xc : pending_xors)
    {
      // Ensure variables exist
      for(unsigned v : xc.vars)
        while(solver->nVars() <= v)
          solver->new_var();
      solver->add_xor_clause(xc.vars, xc.rhs);
    }
    xors_added = true;
    
  }

  // Build assumptions
  std::vector<CMSat::Lit> cms_assumptions;
  cms_assumptions.reserve(assumptions.size());
  for(const auto &lit : assumptions)
  {
    if(lit.is_constant())
    {
      if(lit.is_false())
        return resultt::P_UNSATISFIABLE;
      continue;
    }
    unsigned cms_var = lit.var_no() - 1;
    while(solver->nVars() <= cms_var)
      solver->new_var();
    cms_assumptions.emplace_back(cms_var, lit.sign());
  }

  CMSat::lbool ret = solver->solve(&cms_assumptions);

  if(ret == CMSat::l_True)
  {
    status = statust::SAT;
    return resultt::P_SATISFIABLE;
  }
  else if(ret == CMSat::l_False)
  {
    status = statust::UNSAT;
    return resultt::P_UNSATISFIABLE;
  }
  else
  {
    status = statust::ERROR;
    return resultt::P_ERROR;
  }
}

tvt satcheck_cryptominisatt::l_get(literalt a) const
{
  if(a.is_true())
    return tvt{true};
  if(a.is_false())
    return tvt{false};

  unsigned var = a.var_no();
  if(var == 0 || status != statust::SAT)
    return tvt{tvt::tv_enumt::TV_UNKNOWN};

  unsigned cms_var = var - 1;
  if(cms_var >= solver->nVars())
    return tvt{tvt::tv_enumt::TV_UNKNOWN};

  const auto &model = solver->get_model();
  if(cms_var >= model.size())
    return tvt{tvt::tv_enumt::TV_UNKNOWN};

  CMSat::lbool val = model[cms_var];
  if(val == CMSat::l_True)
    return a.sign() ? tvt{false} : tvt{true};
  if(val == CMSat::l_False)
    return a.sign() ? tvt{true} : tvt{false};
  return tvt{tvt::tv_enumt::TV_UNKNOWN};
}

bool satcheck_cryptominisatt::is_in_conflict(literalt a) const
{
  if(a.is_constant())
    return false;

  unsigned cms_var = a.var_no() - 1;
  const auto &conflict = solver->get_conflict();
  for(const auto &lit : conflict)
  {
    if(lit.var() == cms_var)
      return true;
  }
  return false;
}

#endif // HAVE_CRYPTOMINISAT
