/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/threeval.h>

#include "satcheck_precosat.h"

#include <precosat.hh>

#ifndef HAVE_PRECOSAT
#error "Expected HAVE_PRECOSAT"
#endif

#define precosat_lit(a) ((a).var_no()*2 + !(a).sign())

/*******************************************************************\

Function: satcheck_precosatt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_precosatt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no()>solver->getMaxVar())
    return tvt(tvt::TV_UNKNOWN);

  const int val=solver->val(precosat_lit(a));
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::TV_UNKNOWN);

  return result;
}

/*******************************************************************\

Function: satcheck_precosatt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_precosatt::solver_text()
{
  return "PrecoSAT";
}

/*******************************************************************\

Function: satcheck_precosatt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_precosatt::lcnf(const bvt &bv)
{
  bvt new_bv;
  
  if(process_clause(bv, new_bv))
    return;

  forall_literals(it, new_bv)
    solver->add(precosat_lit(*it));

  solver->add(0);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_precosatt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_precosatt::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(solver->getAddedOrigClauses())+" clauses";
    messaget::status(msg);
  }
  
  std::string msg;

  const int res=solver->solve();
  if(res==1)
  {
    msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    assert(res==-1);
    msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_precosatt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_precosatt::set_assignment(literalt a, bool value)
{
  assert(false);
}

/*******************************************************************\

Function: satcheck_precosatt::satcheck_precosatt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_precosatt::satcheck_precosatt() :
  solver(new PrecoSat::Solver())
{
  solver->init();
}

/*******************************************************************\

Function: satcheck_precosatt::~satcheck_precosatt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_precosatt::~satcheck_precosatt()
{
  delete solver;
}

/*******************************************************************\

Function: satcheck_precosatt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/*
void satcheck_precosatt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}
*/

