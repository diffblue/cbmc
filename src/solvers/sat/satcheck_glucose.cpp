/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef _MSC_VER
#include <inttypes.h>
#endif

#include <cassert>
#include <stack>

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

  forall_literals(it, bv)
    if(!it->is_false())
      dest.push(Glucose::mkLit(it->var_no(), it->sign()));
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
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  using Glucose::lbool;

  if(solver->model[a.var_no()]==l_True)
    result=tvt(true);
  else if(solver->model[a.var_no()]==l_False)
    result=tvt(false);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  if(a.sign())
    result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_glucose_baset::set_polarity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<typename T>
void satcheck_glucose_baset<T>::set_polarity(literalt a, bool value)
{
  assert(!a.is_constant());
  add_variables();
  solver->setPolarity(a.var_no(), value);
}

/*******************************************************************\

Function: satcheck_glucose_no_simplifiert::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_glucose_no_simplifiert::solver_text()
{
  return "Glucose Syrup without simplifier";
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_glucose_simplifiert::solver_text()
{
  return "Glucose Syrup with simplifier";
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

  // We start counting at 1, thus there is one variable fewer.
  {
    messaget::status() <<
      (no_variables()-1) << " variables, " <<
      solver->nClauses() << " clauses" << eom;
  }

  add_variables();

  if(!solver->okay())
  {
    messaget::status() <<
      "SAT checker inconsistent: instance is UNSATISFIABLE" << eom;
  }
  else
  {
    // if assumptions contains false, we need this to be UNSAT
    bool has_false=false;

    forall_literals(it, assumptions)
      if(it->is_false())
        has_false=true;

    if(has_false)
    {
      messaget::status() <<
        "got FALSE as assumption: instance is UNSATISFIABLE" << eom;
    }
    else
    {
      Glucose::vec<Glucose::Lit> solver_assumptions;
      convert(assumptions, solver_assumptions);

      if(solver->solve(solver_assumptions))
      {
        messaget::status() <<
          "SAT checker: instance is SATISFIABLE" << eom;
        assert(solver->model.size()!=0);
        status=SAT;
        return P_SATISFIABLE;
      }
      else
      {
        messaget::status() <<
          "SAT checker: instance is UNSATISFIABLE" << eom;
      }
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

  // MiniSat2 kills the model in case of UNSAT
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
satcheck_glucose_baset<T>::satcheck_glucose_baset(T *_solver):
  solver(_solver)
{
}

/*******************************************************************\

Function: satcheck_glucose_baset::~satcheck_glucose_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<>
satcheck_glucose_baset<Glucose::Solver>::~satcheck_glucose_baset()
{
  delete solver;
}

template<>
satcheck_glucose_baset<Glucose::SimpSolver>::~satcheck_glucose_baset()
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

Function: satcheck_glucose_no_simplifiert::satcheck_glucose_no_simplifiert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_glucose_no_simplifiert::satcheck_glucose_no_simplifiert():
  satcheck_glucose_baset<Glucose::Solver>(new Glucose::Solver)
{
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::satcheck_glucose_simplifiert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_glucose_simplifiert::satcheck_glucose_simplifiert():
  satcheck_glucose_baset<Glucose::SimpSolver>(new Glucose::SimpSolver)
{
}

/*******************************************************************\

Function: satcheck_glucose_simplifiert::set_frozen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_glucose_simplifiert::set_frozen(literalt a)
{
  if(!a.is_constant())
  {
    add_variables();
    solver->setFrozen(a.var_no(), true);
  }
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
