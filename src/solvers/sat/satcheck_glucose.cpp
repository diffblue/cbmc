/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef _MSC_VER
#include <inttypes.h>
#endif

#include <cassert>
#include <stack>

#include <util/i2string.h>
#include <util/threeval.h>

#include "satcheck_glucose.h"

#include <core/Solver.h>
#include <simp/SimpSolver.h>

#ifndef HAVE_GLUCOSE
#error "Expected HAVE_GLUCOSE"
#endif

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(const bvt &bv, Glucose::vec<Glucose::Lit> &dest)
{
  dest.capacity(bv.size());

  for(unsigned i=0; i<bv.size(); i++)
    if(!bv[i].is_false())
      dest.push(Glucose::mkLit(bv[i].var_no(), bv[i].sign()));
}

/*******************************************************************\

Function: satcheck_glucose_baset::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
tvt satcheck_glucose_baset<T>::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  if(a.var_no()>=(unsigned)solver->model.size())
    return tvt(tvt::TV_UNKNOWN);

  using Glucose::lbool;

  if(solver->model[a.var_no()]==l_True)
    result=tvt(true);
  else if(solver->model[a.var_no()]==l_False)
    result=tvt(false);
  else
    return tvt(tvt::TV_UNKNOWN);
  
  if(a.sign()) result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_glucose_no_simplifiert::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_glucose_no_simplifiert::solver_text()
{
  return "Glucose 2.2 without simplifier";
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_glucose_simplifiert::solver_text()
{
  return "Glucose 2.2 with simplifier";
}

/*******************************************************************\

Function: satcheck_glucose_baset::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
void satcheck_glucose_baset<T>::add_variables()
{
  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

/*******************************************************************\

Function: satcheck_glucose_baset::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
void satcheck_glucose_baset<T>::lcnf(const bvt &bv)
{
  add_variables();

  forall_literals(it, bv)
  {
    if(it->is_true())
      return;
    else if(!it->is_false())
      assert(it->var_no()<(unsigned)solver->nVars());
  }
    
  Glucose::vec<Glucose::Lit> c;

  convert(bv, c);

  // Glucose can't do empty clauses
  if(c.empty())
  {
    empty_clause_added=true;
    return;
  }

  // Note the underscore.
  // Add a clause to the solver without making superflous internal copy.
  
  solver->addClause_(c);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_glucose_baset::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
propt::resultt satcheck_glucose_baset<T>::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(solver->nClauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }
  
  add_variables();
  
  std::string msg;

  if(empty_clause_added)
  {
    msg="empty clause: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status() << msg << messaget::eom
  }
  else if(!solver->okay())
  {
    msg="SAT checker inconsistent: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status() << msg << messaget::eom;
  }
  else
  {
    Glucose::vec<Glucose::Lit> solver_assumptions;
    convert(assumptions, solver_assumptions);

    if(solver->solve(solver_assumptions))
    {
      msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
      messaget::status() << msg << messaget::eom;
      assert(solver->!model.empty());
      status=SAT;
      return P_SATISFIABLE;
    }
    else
    {
      msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
      messaget::status() << msg << messaget::eom;
    }
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_glucose_baset::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
void satcheck_glucose_baset<T>::set_assignment(literalt a, bool value)
{
  assert(!a.is_constant());

  unsigned v=a.var_no();
  bool sign=a.sign();

  // MiniSat2/Glucose kill the model in case of UNSAT
  solver->model.growTo(v+1);
  value^=sign;
  solver->model[v]=Glucose::lbool(value);
}

/*******************************************************************\

Function: satcheck_glucose_baset::satcheck_glucose_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
satcheck_glucose_baset<T>::satcheck_glucose_baset()
{
  empty_clause_added=false;
  solver=NULL;
}

/*******************************************************************\

Function: satcheck_glucose_no_simplifiert::satcheck_glucose_no_simplifiert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_glucose_no_simplifiert::satcheck_glucose_no_simplifiert()
{
  solver=new Glucose::Solver;
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::satcheck_glucose_simplifiert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_glucose_simplifiert::satcheck_glucose_simplifiert()
{
  solver=new Glucose::SimpSolver;
}

/*******************************************************************\

Function: satcheck_glucose_baset::~satcheck_glucose_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
satcheck_glucose_baset<T>::~satcheck_glucose_baset()
{
  delete solver;
}

/*******************************************************************\

Function: satcheck_glucose_baset::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
bool satcheck_glucose_baset<T>::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  for(int i=0; i<solver->conflict.size(); i++)
    if(var(solver->conflict[i])==v)
      return true;

  return false;
}

/*******************************************************************\

Function: satcheck_glucose_baset::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
void satcheck_glucose_baset<T>::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::set_frozen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_glucose_simplifiert::set_frozen(literalt a)
{
  assert(!a.is_constant());

  solver->setFrozen(a.var_no(), true);
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::is_eliminated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_glucose_simplifiert::is_eliminated(literalt a) const
{
  assert(!a.is_constant());

  return solver->isEliminated(a.var_no());
}

