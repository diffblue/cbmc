/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>
#include <inttypes.h>

#include <stack>

#include <i2string.h>

#include "satcheck_minisat2.h"

#include <core/Solver.h>
#include <simp/SimpSolver.h>

#ifndef HAVE_MINISAT2
#error "Expected HAVE_MINISAT2"
#endif

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(const bvt &bv, Minisat::vec<Minisat::Lit> &dest)
{
  dest.growTo(bv.size());
  
  for(unsigned i=0; i<bv.size(); i++)
    dest[i]=Minisat::mkLit(bv[i].var_no(), bv[i].sign());
}

/*******************************************************************\

Function: satcheck_minisat_baset::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_minisat_baset::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  if(a.var_no()>=(unsigned)solver->model.size())
    return tvt(tvt::TV_UNKNOWN);

  using Minisat::lbool;

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

Function: satcheck_minisat_baset::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat_baset::solver_text()
{
  return "MiniSAT2 (base)";
}

/*******************************************************************\

Function: satcheck_minisat_coret::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat_coret::solver_text()
{
  return "MiniSAT2 without simplifier";
}

/*******************************************************************\

Function: satcheck_minisat_simpt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat_simpt::solver_text()
{
  return "MiniSAT2 with simplifier";
}

/*******************************************************************\

Function: satcheck_minisat_baset::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat_baset::add_variables()
{
  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

/*******************************************************************\

Function: satcheck_minisat_baset::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat_baset::lcnf(const bvt &bv)
{
  bvt new_bv;
  
  if(process_clause(bv, new_bv))
    return;
    
  // Minisat can't do empty clauses
  if(new_bv.empty())
  {
    empty_clause_added=true;
    return;
  }

  add_variables();

  Minisat::vec<Minisat::Lit> c;
  convert(new_bv, c);

  for(unsigned i=0; i<new_bv.size(); i++)
    assert(new_bv[i].var_no()<(unsigned)solver->nVars());

  solver->addClause(c);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_minisat_baset::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_minisat_baset::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(solver->nClauses())+" clauses";
    messaget::status(msg);
  }
  
  add_variables();
  
  std::string msg;

  if(empty_clause_added)
  {
    msg="empty clause: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  }
  else if(!solver->okay())
  {
    msg="SAT checker inconsistent: negated claim is UNSATISFIABLE, i.e., holds";
    messaget::status(msg);
  }
  else
  {
    Minisat::vec<Minisat::Lit> MiniSat_assumptions;
    convert(assumptions, MiniSat_assumptions);

    if(solver->solve(MiniSat_assumptions))
    {
      msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
      messaget::status(msg);
      assert(solver->model.size()!=0);
      status=SAT;
      return P_SATISFIABLE;
    }
    else
    {
      msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
      messaget::status(msg);
    }
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_minisat_baset::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat_baset::set_assignment(literalt a, bool value)
{
  assert(!a.is_constant());

  unsigned v=a.var_no();
  bool sign=a.sign();

  // MiniSat2 kills the model in case of UNSAT
  solver->model.growTo(v+1);
  value^=sign;
  solver->model[v]=Minisat::lbool(value);
}

/*******************************************************************\

Function: satcheck_minisat_coret::satcheck_minisatt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat_coret::satcheck_minisat_coret()
{
  solver=new Minisat::Solver;
}

/*******************************************************************\

Function: satcheck_minisat_simpt::satcheck_minisat_simpt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat_simpt::satcheck_minisat_simpt()
{
  solver=new Minisat::SimpSolver;
}

/*******************************************************************\

Function: satcheck_minisat_baset::~satcheck_minisat_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat_baset::~satcheck_minisat_baset()
{
  delete solver;
}

/*******************************************************************\

Function: satcheck_minisat_baset::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_minisat_baset::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  for(int i=0; i<solver->conflict.size(); i++)
    if(var(solver->conflict[i])==v)
      return true;

  return false;
}

/*******************************************************************\

Function: satcheck_minisat_baset::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat_baset::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  for(bvt::const_iterator it=assumptions.begin();
      it!=assumptions.end();
      it++)
    assert(!it->is_constant());
}

