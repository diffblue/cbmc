/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/i2string.h>

#include "satcheck_zchaff.h"

#include <zchaff_solver.h>

//#define DEBUG

/*******************************************************************\

Function: satcheck_zchaff_baset::satcheck_zchaff_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zchaff_baset::satcheck_zchaff_baset(CSolver *_solver):solver(_solver)
{
  status=INIT;
  solver->set_randomness(0);
  solver->set_variable_number(0);
}

/*******************************************************************\

Function: satcheck_zchaff_baset::~satcheck_zchaff_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zchaff_baset::~satcheck_zchaff_baset()
{
}

/*******************************************************************\

Function: satcheck_zchaff_baset::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_zchaff_baset::l_get(literalt a) const
{
  assert(status==SAT);

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  assert(a.var_no()<solver->variables().size());

  switch(solver->variable(a.var_no()).value())
  {
   case 0: result=tvt(false); break;
   case 1: result=tvt(true); break;
   default: result=tvt(tvt::TV_UNKNOWN); break;
  }

  if(a.sign()) result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_zchaff_baset::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_zchaff_baset::solver_text()
{
  return solver->version();
}

/*******************************************************************\

Function: satcheck_zchaff_baset::copy_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_zchaff_baset::copy_cnf()
{
  assert(status==INIT);

  // this can only be called once
  solver->set_variable_number(no_variables());

  for(clausest::const_iterator it=clauses.begin();
      it!=clauses.end();
      it++)
    solver->add_orig_clause((int *)&((*it)[0]), it->size());
}

/*******************************************************************\

Function: satcheck_zchaff_baset::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_zchaff_baset::prop_solve()
{
  // this is *not* incremental
  assert(status==INIT);
  
  copy_cnf();

  {
    std::string msg=
      i2string(solver->num_variables())+" variables, "+
      i2string(solver->clauses().size())+" clauses";
    messaget::status(msg);
  }

  SAT_StatusT result=(SAT_StatusT)solver->solve();

  {
    std::string msg;

    switch(result)
    {
     case UNSATISFIABLE:
      msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
      break;

     case SATISFIABLE:
      msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
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

    messaget::status(msg);
  }

  if(result==SATISFIABLE)
  {
    // see if it is complete
    for(unsigned i=1; i<solver->variables().size(); i++)
      assert(solver->variables()[i].value()==0 ||
             solver->variables()[i].value()==1);
  }

  #ifdef DEBUG
  if(result==SATISFIABLE)
  {
    for(unsigned i=2; i<(_no_variables*2); i+=2)
      cout << "DEBUG L" << i << ":" << get(i) << endl;
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

/*******************************************************************\

Function: satcheck_zchaff_baset::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_zchaff_baset::set_assignment(literalt a, bool value)
{
  unsigned v=a.var_no();
  bool sign=a.sign();
  value^=sign;
  solver->variables()[v].set_value(value);
}

/*******************************************************************\

Function: satcheck_zchafft::satcheck_zchafft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zchafft::satcheck_zchafft():
  satcheck_zchaff_baset(new CSolver)
{
}

/*******************************************************************\

Function: satcheck_zchafft::~satcheck_zchafft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_zchafft::~satcheck_zchafft()
{
  delete solver;
}
