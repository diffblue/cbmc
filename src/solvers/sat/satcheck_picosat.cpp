/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>
#include <util/threeval.h>

#include "satcheck_picosat.h"

extern "C" {
#include <picosat.h>
}

#ifndef HAVE_PICOSAT
#error "Expected HAVE_PICOSAT"
#endif

/*******************************************************************\

Function: satcheck_picosatt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_picosatt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no()>picosat_variables())
    return tvt(tvt::TV_UNKNOWN);

  const int val=picosat_deref(a.dimacs());
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::TV_UNKNOWN);

  return result;
}

/*******************************************************************\

Function: satcheck_picosatt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_picosatt::solver_text()
{
  return "PicoSAT";
}

/*******************************************************************\

Function: satcheck_picosatt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_picosatt::lcnf(const bvt &bv)
{
  bvt new_bv;
  
  if(process_clause(bv, new_bv))
    return;

  picosat_adjust(_no_variables);

  forall_literals(it, new_bv)
    picosat_add(it->dimacs());

  picosat_add(0);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_picosatt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_picosatt::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(picosat_added_original_clauses())+" clauses";
    messaget::status(msg);
  }
  
  std::string msg;

  forall_literals(it, assumptions)
    picosat_assume(it->dimacs());

  const int res=picosat_sat(-1);
  if(res==PICOSAT_SATISFIABLE)
  {
    msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
    messaget::status(msg);
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    assert(res==PICOSAT_UNSATISFIABLE);
    msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_picosatt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_picosatt::set_assignment(literalt a, bool value)
{
  assert(false);
}

/*******************************************************************\

Function: satcheck_picosatt::satcheck_picosatt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_picosatt::satcheck_picosatt()
{
  picosat_init();
}

/*******************************************************************\

Function: satcheck_picosatt::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_picosatt::is_in_conflict(literalt a) const
{
  assert(!a.is_constant());

  return picosat_failed_assumption(a.dimacs())!=0;
}

/*******************************************************************\

Function: satcheck_picosatt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_picosatt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}

