/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <cassert>

#include <i2string.h>
#include <threeval.h>

#include "satcheck_lingeling.h"

extern "C" {
#include <lglib.h>
}

#ifndef HAVE_LINGELING
#error "Expected HAVE_LINGELING"
#endif

/*******************************************************************\

Function: satcheck_lingelingt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_lingelingt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no()>lglmaxvar(solver))
    return tvt(tvt::TV_UNKNOWN);

  const int val=lglderef(solver, a.dimacs());
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::TV_UNKNOWN);

  return result;
}

/*******************************************************************\

Function: satcheck_lingelingt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_lingelingt::solver_text()
{
  return "Lingeling";
}

/*******************************************************************\

Function: satcheck_lingelingt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: satcheck_lingelingt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_lingelingt::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(clause_counter)+" clauses";
    messaget::status(msg);
  }
  
  std::string msg;

  forall_literals(it, assumptions)
    lglassume(solver, it->dimacs());

  const int res=lglsat(solver);
  if(res==10)
  {
    msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    assert(res==20);
    msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_lingelingt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_lingelingt::set_assignment(literalt a, bool value)
{
  assert(false);
}

/*******************************************************************\

Function: satcheck_lingelingt::satcheck_lingelingt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_lingelingt::satcheck_lingelingt() :
  solver(lglinit())
{
}

/*******************************************************************\

Function: satcheck_lingelingt::satcheck_lingelingt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_lingelingt::~satcheck_lingelingt()
{
  lglrelease(solver);
  solver=0;
}

/*******************************************************************\

Function: satcheck_lingelingt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_lingelingt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}

