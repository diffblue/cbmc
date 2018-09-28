/*******************************************************************\

Module: External SAT Solver Binding

Author: Norbert Manthey, nmanthey@amazon.com

\*******************************************************************/

#ifndef _MSC_VER
#include <inttypes.h>
#endif

#include <algorithm>
#include <stack>

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/threeval.h>

#include "satcheck_ipasir.h"

#ifdef HAVE_IPASIR

extern "C"
{
#include <ipasir.h>
}

/*

Interface description:
https://github.com/biotomas/ipasir/blob/master/ipasir.h

Representation:
Variables for a formula start with 1! 0 is used as termination symbol.

*/

tvt satcheck_ipasirt::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  // compare to internal no_variables number
  if(a.var_no()>=(unsigned)no_variables())
    return tvt::unknown();

  const int val=ipasir_val(solver, a.var_no());

  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt::unknown();

  if(a.sign())
    result=!result;

  return result;
}

const std::string satcheck_ipasirt::solver_text()
{
  return std::string(ipasir_signature());
}

void satcheck_ipasirt::lcnf(const bvt &bv)
{
  forall_literals(it, bv)
  {
    if(it->is_true())
      return;
    else if(!it->is_false())
      INVARIANT(it->var_no()<(unsigned)no_variables(),
             "reject out of bound variables");
  }

  forall_literals(it, bv)
  {
    if(!it->is_false())
    {
      // add literal with correct sign
      ipasir_add(solver, it->dimacs());
    }
  }
  ipasir_add(solver, 0); // terminate clause

  clause_counter++;
}

propt::resultt satcheck_ipasirt::prop_solve()
{
  INVARIANT(status!=statust::ERROR, "there cannot be an error");

  {
    messaget::status() <<
      (no_variables()-1) << " variables, " <<
      clause_counter << " clauses" << eom;
  }

  // use the internal representation, as ipasir does not support reporting the
  // status
  if(status==statust::UNSAT)
  {
    messaget::status() <<
      "SAT checker inconsistent: instance is UNSATISFIABLE" << eom;
  }
  else
  {
    // if assumptions contains false, we need this to be UNSAT
    bvt::const_iterator it = std::find_if(assumptions.begin(),
      assumptions.end(), is_false);
    const bool has_false = it != assumptions.end();

    if(has_false)
    {
      messaget::status() <<
        "got FALSE as assumption: instance is UNSATISFIABLE" << eom;
    }
    else
    {
      forall_literals(it, assumptions)
        if(!it->is_false())
          ipasir_assume(solver, it->dimacs());

      // solve the formula, and handle the return code (10=SAT, 20=UNSAT)
      int solver_state=ipasir_solve(solver);
      if(10==solver_state)
      {
        messaget::status() <<
          "SAT checker: instance is SATISFIABLE" << eom;
        status=statust::SAT;
        return resultt::P_SATISFIABLE;
      }
      else if(20==solver_state)
      {
        messaget::status() <<
          "SAT checker: instance is UNSATISFIABLE" << eom;
      }
      else
      {
        messaget::status() <<
          "SAT checker: solving returned without solution" << eom;
        throw analysis_exceptiont(
          "solving inside IPASIR SAT solver has been interrupted");
      }
    }
  }

  status=statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

void satcheck_ipasirt::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

satcheck_ipasirt::satcheck_ipasirt()
: solver(nullptr)
{
  INVARIANT(!solver, "there cannot be a solver already");
  solver=ipasir_init();
}

satcheck_ipasirt::~satcheck_ipasirt()
{
  if(solver)
    ipasir_release(solver);
  solver=nullptr;
}

bool satcheck_ipasirt::is_in_conflict(literalt a) const
{
  return ipasir_failed(solver, a.var_no());
}

void satcheck_ipasirt::set_assumptions(const bvt &bv)
{
  bvt::const_iterator it = std::find_if(bv.begin(), bv.end(), is_true);
  const bool has_true = it != bv.end();

  if(has_true)
  {
    assumptions.clear();
    return;
  }
  // only copy assertions, if there is no false in bt parameter
  assumptions=bv;
}

#endif
