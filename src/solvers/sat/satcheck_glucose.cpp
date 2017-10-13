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

void convert(const bvt &bv, Glucose::vec<Glucose::Lit> &dest)
{
  dest.capacity(bv.size());

  forall_literals(it, bv)
    if(!it->is_false())
      dest.push(Glucose::mkLit(it->var_no(), it->sign()));
}

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

template<typename T>
void satcheck_glucose_baset<T>::set_polarity(literalt a, bool value)
{
  assert(!a.is_constant());
  add_variables();
  solver->setPolarity(a.var_no(), value);
}

const std::string satcheck_glucose_no_simplifiert::solver_text()
{
  return "Glucose Syrup without simplifier";
}

const std::string satcheck_glucose_simplifiert::solver_text()
{
  return "Glucose Syrup with simplifier";
}

template<typename T>
void satcheck_glucose_baset<T>::add_variables()
{
  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

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

template<typename T>
propt::resultt satcheck_glucose_baset<T>::prop_solve()
{
  assert(status!=statust::ERROR);

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
        status=statust::SAT;
        return resultt::P_SATISFIABLE;
      }
      else
      {
        messaget::status() <<
          "SAT checker: instance is UNSATISFIABLE" << eom;
      }
    }
  }

  status=statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

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

template<typename T>
satcheck_glucose_baset<T>::satcheck_glucose_baset(T *_solver):
  solver(_solver)
{
}

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

template<typename T>
bool satcheck_glucose_baset<T>::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  for(int i=0; i<solver->conflict.size(); i++)
    if(var(solver->conflict[i])==v)
      return true;

  return false;
}

template<typename T>
void satcheck_glucose_baset<T>::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}

satcheck_glucose_no_simplifiert::satcheck_glucose_no_simplifiert():
  satcheck_glucose_baset<Glucose::Solver>(new Glucose::Solver)
{
}

satcheck_glucose_simplifiert::satcheck_glucose_simplifiert():
  satcheck_glucose_baset<Glucose::SimpSolver>(new Glucose::SimpSolver)
{
}

void satcheck_glucose_simplifiert::set_frozen(literalt a)
{
  if(!a.is_constant())
  {
    add_variables();
    solver->setFrozen(a.var_no(), true);
  }
}

bool satcheck_glucose_simplifiert::is_eliminated(literalt a) const
{
  assert(!a.is_constant());

  return solver->isEliminated(a.var_no());
}
