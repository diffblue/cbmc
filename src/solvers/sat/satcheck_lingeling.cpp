/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include "satcheck_lingeling.h"

#include <algorithm>

#include <util/invariant.h>
#include <util/threeval.h>

extern "C"
{
#include <lglib.h>
}

#ifndef HAVE_LINGELING
#error "Expected HAVE_LINGELING"
#endif

tvt satcheck_lingelingt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no()>lglmaxvar(solver))
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val=lglderef(solver, a.dimacs());
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  return result;
}

const std::string satcheck_lingelingt::solver_text()
{
  return "Lingeling";
}

void satcheck_lingelingt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  forall_literals(it, new_bv)
    lgladd(solver, it->dimacs());

  lgladd(solver, 0);

  clause_counter++;
}

propt::resultt satcheck_lingelingt::prop_solve()
{
  PRECONDITION(status != ERROR);

  // We start counting at 1, thus there is one variable fewer.
  {
    std::string msg=
      std::to_string(no_variables()-1)+" variables, "+
      std::to_string(clause_counter)+" clauses";
    messaget::statistics() << msg << messaget::eom;
  }

  std::string msg;

  forall_literals(it, assumptions)
    lglassume(solver, it->dimacs());

  const int res=lglsat(solver);
  CHECK_RETURN(res == 10 || res == 20);

  if(res==10)
  {
    msg="SAT checker: instance is SATISFIABLE";
    messaget::status() << msg << messaget::eom;
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    INVARIANT(res == 20, "result value is either 10 or 20");
    msg="SAT checker: instance is UNSATISFIABLE";
    messaget::status() << msg << messaget::eom;
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

void satcheck_lingelingt::set_assignment(literalt a, bool value)
{
  UNREACHABLE;
}

satcheck_lingelingt::satcheck_lingelingt() :
  solver(lglinit())
{
}

satcheck_lingelingt::~satcheck_lingelingt()
{
  lglrelease(solver);
  solver=0;
}

void satcheck_lingelingt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  INVARIANT(
    std::all_of(
      assumptions.begin(),
      assumptions.end(),
      [](const literalt &l) { return !l.is_constant(); }),
    "assumptions should be non-constant");
}

void satcheck_lingelingt::set_frozen(literalt a)
{
  if(!a.is_constant())
    lglfreeze(solver, a.dimacs());
}

/// Returns true if an assumed literal is in conflict if the formula is UNSAT.
///
/// NOTE: if the literal is not in the assumption it causes an
/// assertion failure in lingeling.
bool satcheck_lingelingt::is_in_conflict(literalt a) const
{
  PRECONDITION(!a.is_constant());
  return lglfailed(solver, a.dimacs())!=0;
}
