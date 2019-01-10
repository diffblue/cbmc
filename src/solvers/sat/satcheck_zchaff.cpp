/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck_zchaff.h"

#include <util/invariant.h>

#include <zchaff_solver.h>

satcheck_zchaff_baset::satcheck_zchaff_baset(CSolver *_solver):solver(_solver)
{
  status=INIT;
  solver->set_randomness(0);
  solver->set_variable_number(0);
}

satcheck_zchaff_baset::~satcheck_zchaff_baset()
{
}

tvt satcheck_zchaff_baset::l_get(literalt a) const
{
  PRECONDITION(status == SAT);

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  INVARIANT(
    a.var_no() < solver->variables().size(),
    "variable number shall be within bounds");

  switch(solver->variable(a.var_no()).value())
  {
    case 0: result=tvt(false); break;
    case 1: result=tvt(true); break;
    default: result=tvt(tvt::tv_enumt::TV_UNKNOWN); break;
  }

  if(a.sign())
    result=!result;

  return result;
}

const std::string satcheck_zchaff_baset::solver_text()
{
  return solver->version();
}

void satcheck_zchaff_baset::copy_cnf()
{
  PRECONDITION(status == INIT);

  // this can only be called once
  solver->set_variable_number(no_variables());

  for(clausest::const_iterator it=clauses.begin();
      it!=clauses.end();
      it++)
    solver->add_orig_clause(
      reinterpret_cast<int*>(&((*it)[0])), it->size());
}

propt::resultt satcheck_zchaff_baset::prop_solve()
{
  // this is *not* incremental
  PRECONDITION(status == INIT);

  copy_cnf();

  {
    std::string msg=
      std::to_string(solver->num_variables())+" variables, "+
      std::to_string(solver->clauses().size())+" clauses";
    messaget::statistics() << msg << messaget::eom;
  }

  SAT_StatusT result=(SAT_StatusT)solver->solve();

  {
    std::string msg;

    switch(result)
    {
     case UNSATISFIABLE:
      msg="SAT checker: instance is UNSATISFIABLE";
      break;

     case SATISFIABLE:
      msg="SAT checker: instance is SATISFIABLE";
      break;

     case UNDETERMINED:
      msg="SAT checker failed: UNDETERMINED";
      break;

     case TIME_OUT:
      msg="SAT checker failed: Time out";
      break;

     case MEM_OUT:
      msg="SAT checker failed: Out of memory";
      break;

     case ABORTED:
      msg="SAT checker failed: ABORTED";
      break;

     default:
      msg="SAT checker failed: unknown result";
      break;
    }

    messaget::status() << msg << messaget::eom;
  }

  if(result==SATISFIABLE)
  {
    // see if it is complete
    for(unsigned i=1; i<solver->variables().size(); i++)
      INVARIANT(
        solver->variables()[i].value() == 0 ||
          solver->variables()[i].value() == 1,
        "all variables shall have been assigned");
  }

  #ifdef DEBUG
  if(result==SATISFIABLE)
  {
    for(unsigned i=2; i<(_no_variables*2); i+=2)
      cout << "DEBUG L" << i << ":" << get(i) << '\n';
  }
  #endif

  if(result==UNSATISFIABLE)
  {
    status=UNSAT;
    return P_UNSATISFIABLE;
  }

  if(result==SATISFIABLE)
  {
    status=SAT;
    return P_SATISFIABLE;
  }

  status=ERROR;

  return P_ERROR;
}

void satcheck_zchaff_baset::set_assignment(literalt a, bool value)
{
  unsigned v=a.var_no();
  bool sign=a.sign();
  value^=sign;
  solver->variables()[v].set_value(value);
}

satcheck_zchafft::satcheck_zchafft():
  satcheck_zchaff_baset(new CSolver)
{
}

satcheck_zchafft::~satcheck_zchafft()
{
  delete solver;
}
