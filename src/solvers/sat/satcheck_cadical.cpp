/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "satcheck_cadical.h"

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/threeval.h>

#ifdef HAVE_CADICAL

#include <cadical.hpp>

tvt satcheck_cadicalt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no() > static_cast<unsigned>(solver->max()))
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

  clause_counter++;
}

propt::resultt satcheck_cadicalt::prop_solve()
{
  INVARIANT(status != statust::ERROR, "there cannot be an error");

  messaget::statistics() << (no_variables() - 1) << " variables, "
                         << clause_counter << " clauses" << eom;

  if(status == statust::UNSAT)
  {
    messaget::status() << "SAT checker inconsistent: instance is UNSATISFIABLE"
                       << eom;
  }
  else
  {
    switch(solver->solve())
    {
      case 10:
        messaget::status() << "SAT checker: instance is SATISFIABLE" << eom;
        status = statust::SAT;
        return resultt::P_SATISFIABLE;
      case 20:
        messaget::status() << "SAT checker: instance is UNSATISFIABLE" << eom;
        break;
      default:
        messaget::status() << "SAT checker: solving returned without solution"
                           << eom;
        throw analysis_exceptiont(
          "solving inside CaDiCaL SAT solver has been interrupted");
    }
  }

  status = statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

void satcheck_cadicalt::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

satcheck_cadicalt::satcheck_cadicalt() :
  solver(new CaDiCaL::Solver())
{
  solver->set("quiet", 1);
}

satcheck_cadicalt::~satcheck_cadicalt()
{
  delete solver;
}

void satcheck_cadicalt::set_assumptions(const bvt &bv)
{
  INVARIANT(false, "method not supported");
}

bool satcheck_cadicalt::is_in_conflict(literalt a) const
{
  INVARIANT(false, "method not supported");
  return false;
}

#endif
