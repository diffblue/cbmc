/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck_booleforce.h"

#include <util/invariant.h>

extern "C"
{
#include "booleforce.h"
}

satcheck_booleforcet::satcheck_booleforcet()
{
  booleforce_set_trace(false);
}

satcheck_booleforce_coret::satcheck_booleforce_coret()
{
  booleforce_set_trace(true);
}

satcheck_booleforce_baset::~satcheck_booleforce_baset()
{
  booleforce_reset();
}

tvt satcheck_booleforce_baset::l_get(literalt a) const
{
  PRECONDITION(status == SAT);

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;
  unsigned v=a.var_no();
  CHECK_RETURN(v < no_variables());

  int r=booleforce_deref(v);

  if(r>0)
    result=tvt(true);
  else if(r<0)
    result=tvt(false);
  else
    result=tvt(tvt::tv_enumt::TV_UNKNOWN);

  if(a.sign())
    result=!result;

  return result;
}

const std::string satcheck_booleforce_baset::solver_text()
{
  return std::string("Booleforce version ")+booleforce_version();
}

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

propt::resultt satcheck_booleforce_baset::prop_solve()
{
  PRECONDITION(status == SAT || status == INIT);

  int result=booleforce_sat();

  {
    std::string msg;

    switch(result)
    {
    case BOOLEFORCE_UNSATISFIABLE:
      msg="SAT checker: instance is UNSATISFIABLE";
      break;

    case BOOLEFORCE_SATISFIABLE:
      msg="SAT checker: instance is SATISFIABLE";
      break;

    default:
      msg="SAT checker failed: unknown result";
      break;
    }

    messaget::status() << msg << messaget::eom;
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

bool satcheck_booleforce_coret::is_in_core(literalt l) const
{
  return booleforce_var_in_core(l.var_no());
}
