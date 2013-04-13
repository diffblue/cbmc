/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>

#include "satcheck_booleforce.h"

extern "C" {
#include "booleforce.h"
}

/*******************************************************************\

Function: satcheck_booleforcet::satcheck_booleforcet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_booleforcet::satcheck_booleforcet()
{
  booleforce_set_trace(false);
}

/*******************************************************************\

Function: satcheck_booleforce_coret::satcheck_booleforce_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_booleforce_coret::satcheck_booleforce_coret()
{
  booleforce_set_trace(true);
}

/*******************************************************************\

Function: satcheck_booleforce_baset::~satcheck_booleforce_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_booleforce_baset::~satcheck_booleforce_baset()
{
  booleforce_reset();
}

/*******************************************************************\

Function: satcheck_booleforce_baset::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_booleforce_baset::l_get(literalt a) const
{
  assert(status==SAT);

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;
  unsigned v=a.var_no();

  assert(v<no_variables());

  int r=booleforce_deref(v);

  if(r>0)
    result=tvt(true);
  else if(r<0)
    result=tvt(false);
  else
    result=tvt(tvt::TV_UNKNOWN);

  if(a.sign()) result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_booleforce_Baset::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_booleforce_baset::solver_text()
{
  return std::string("Booleforce version ")+booleforce_version();
}

/*******************************************************************\

Function: satcheck_booleforce_baset::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_booleforce_baset::lcnf(const bvt &bv)
{
  bvt tmp;
  
  if(process_clause(bv, tmp))
    return;

  for(unsigned j=0; j<tmp.size(); j++)
    booleforce_add(tmp[j].dimacs());

  // zero-terminated
  booleforce_add(0);
  
  clause_counter++;
}

/*******************************************************************\

Function: satcheck_booleforce_baset::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_booleforce_baset::prop_solve()
{
  assert(status==SAT || status==INIT);

  int result=booleforce_sat();

  {
    std::string msg;

    switch(result)
    {
    case BOOLEFORCE_UNSATISFIABLE:
      msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
      break;

    case BOOLEFORCE_SATISFIABLE:
      msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
      break;

    default:
      msg="SAT checker failed: unknown result";
      break;    
    }

    messaget::status(msg);
  }

  if(result==BOOLEFORCE_UNSATISFIABLE)
  {
    status=UNSAT;
    return P_UNSATISFIABLE;
  }

  if(result==BOOLEFORCE_SATISFIABLE)
  {
    status=SAT;
    return P_SATISFIABLE;
  }
  
  status=ERROR;
 
  return P_ERROR;
}

/*******************************************************************\

Function: satcheck_booleforce_coret::in_core

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_booleforce_coret::is_in_core(literalt l) const
{
  return booleforce_var_in_core(l.var_no());
}
