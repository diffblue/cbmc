/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "satcheck_cadical.h"

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/narrow.h>
#include <util/threeval.h>

#ifdef HAVE_CADICAL

#include <cadical.hpp>

tvt satcheck_cadicalt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no() > narrow<unsigned>(solver->vars()))
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val = solver->val(a.dimacs());
  if(val>0)
    result = tvt(true);
  else if(val<0)
    result = tvt(false);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  return result;
}

const std::string satcheck_cadicalt::solver_text()
{
  return std::string("CaDiCaL ") + solver->version();
}

void satcheck_cadicalt::lcnf(const bvt &bv)
{
  for(const auto &lit : bv)
  {
    if(lit.is_true())
      return;
    else if(!lit.is_false())
      INVARIANT(lit.var_no() < no_variables(), "reject out of bound variables");
  }

  for(const auto &lit : bv)
  {
    if(!lit.is_false())
    {
      // add literal with correct sign
      solver->add(lit.dimacs());
    }
  }
  solver->add(0); // terminate clause

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

propt::resultt satcheck_cadicalt::do_prop_solve()
{
  INVARIANT(status != statust::ERROR, "there cannot be an error");

  log.statistics() << (no_variables() - 1) << " variables, " << clause_counter
                   << " clauses" << messaget::eom;

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
    solver->assume(a.dimacs());

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

void satcheck_cadicalt::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

satcheck_cadicalt::satcheck_cadicalt(message_handlert &message_handler)
  : cnf_solvert(message_handler), solver(new CaDiCaL::Solver())
{
  solver->set("quiet", 1);
}

satcheck_cadicalt::~satcheck_cadicalt()
{
  delete solver;
}

void satcheck_cadicalt::set_assumptions(const bvt &bv)
{
  // We filter out 'true' assumptions which cause spurious results with CaDiCaL.
  assumptions.clear();
  for(const auto &assumption : bv)
  {
    if(!assumption.is_true())
    {
      assumptions.push_back(assumption);
    }
  }
}

bool satcheck_cadicalt::is_in_conflict(literalt a) const
{
  return solver->failed(a.dimacs());
}

#endif
