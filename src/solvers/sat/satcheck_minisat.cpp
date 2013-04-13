/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <stack>

#include <util/i2string.h>
#include <util/threeval.h>

#include "satcheck_minisat.h"

#include <Solver.h>
#include <Proof.h>

#ifndef HAVE_MINISAT
#error "Expected HAVE_MINISAT"
#endif

/*******************************************************************\

Function: convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void convert(const bvt &bv, vec<Lit> &dest)
{
  dest.growTo(bv.size());
  
  for(unsigned i=0; i<bv.size(); i++)
    dest[i]=Lit(bv[i].var_no(), bv[i].sign());
}

/*******************************************************************\

   Class: minisat_prooft

 Purpose:

\*******************************************************************/

class minisat_prooft:public ProofTraverser
{
public:
  virtual void root(const vec<Lit> &c)
  {
    resolution_proof.clauses.push_back(clauset());
    resolution_proof.clauses.back().is_root=true;
    resolution_proof.clauses.back().root_clause.resize(c.size());
//    resolution_proof.clauses.back().pid = resolution_proof.partition_id;

    for(int i=0; i<c.size(); i++)
    {
      resolution_proof.clauses.back().root_clause[i]=
        literalt(var(c[i]), sign(c[i]));
//    if(var(c[i]) > resolution_proof.no_vars)
//      resolution_proof.no_vars = var(c[i]);
    }
  }
  
  virtual void chain(const vec<ClauseId> &cs, const vec<Var> &xs);

  virtual void deleted(ClauseId c) { }
  virtual void done() { }
  virtual ~minisat_prooft() { }
  
  simple_prooft resolution_proof;
};

/*******************************************************************\

Function: minisat_prooft::chain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void minisat_prooft::chain(const vec<ClauseId> &cs, const vec<Var> &xs)
{
  assert(cs.size()==xs.size()+1);

  resolution_proof.clauses.push_back(clauset());
  clauset &c=resolution_proof.clauses.back();

  c.is_root=false;
  // c.pid = resolution_proof.partition_id;
  c.first_clause_id=cs[0];
  c.steps.resize(xs.size());

  // copy clause IDs
  int c_id=resolution_proof.clauses.size();

  for(int i=0; i<xs.size(); i++)
  {
    // must be decreasing
    assert(cs[i]<c_id);
    c.steps[i].clause_id=cs[i+1];
    c.steps[i].pivot_var_no=xs[i];
  }
}

/*******************************************************************\

Function: satcheck_minisat1_baset::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_minisat1_baset::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  assert(a.var_no()!=0);
  assert(a.var_no()<(unsigned)solver->model.size());

  if(solver->model[a.var_no()]==l_True)
    result=tvt(true);
  else if(solver->model[a.var_no()]==l_False)
    result=tvt(false);
  else
    result=tvt(tvt::TV_UNKNOWN);
  
  if(a.sign()) result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_minisat1_baset::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat1_baset::solver_text()
{
  return "MiniSAT 1.14p";
}

/*******************************************************************\

Function: satcheck_minisat1_baset::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat1_baset::add_variables()
{

  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

/*******************************************************************\

Function: satcheck_minisat1_baset::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat1_baset::lcnf(const bvt &bv)
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

  vec<Lit> c;
  convert(new_bv, c);

  for(unsigned i=0; i<new_bv.size(); i++)
    assert(new_bv[i].var_no()<(unsigned)solver->nVars());

  solver->addClause(c);

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_minisat1_baset::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_minisat1_baset::prop_solve()
{
  assert(status!=ERROR);

  {
    std::string msg=
      i2string(_no_variables)+" variables, "+
      i2string(solver->nClauses())+" clauses";
    messaget::status(msg);
  }
  
  add_variables();

  solver->simplifyDB();
  
  std::string msg;

  if(empty_clause_added)
  {
    msg="empty clause: negated claim is UNSATISFIABLE, i.e., holds";
  }
  else if(!solver->okay())
  {
    msg="SAT checker inconsistent: negated claim is UNSATISFIABLE, i.e., holds";
  }
  else
  {
    vec<Lit> MiniSat_assumptions;
    convert(assumptions, MiniSat_assumptions);

    if(solver->solve(MiniSat_assumptions))
    {
      msg="SAT checker: negated claim is SATISFIABLE, i.e., does not hold";
      messaget::status(msg);
      status=SAT;
      return P_SATISFIABLE;
    }
    else
      msg="SAT checker: negated claim is UNSATISFIABLE, i.e., holds";
  }

  messaget::status(msg);
  status=UNSAT;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_minisat1_baset::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat1_baset::set_assignment(literalt a, bool value)
{
  unsigned v=a.var_no();
  bool sign=a.sign();
  solver->model.growTo(v+1);
  value^=sign;
  solver->model[v]=lbool(value);
}

/*******************************************************************\

Function: satcheck_minisat1_baset::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_minisat1_baset::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  for(int i=0; i<solver->conflict.size(); i++)
  {
    if(var(solver->conflict[i])==v)
      return true;
  }

  return false;
}

/*******************************************************************\

Function: satcheck_minisat1_baset::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_minisat1_baset::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  for(bvt::const_iterator it=assumptions.begin();
      it!=assumptions.end();
      it++)
    assert(!it->is_constant());
}

/*******************************************************************\

Function: satcheck_minisat1t::satcheck_minisat1t

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1t::satcheck_minisat1t()
{
  empty_clause_added=false;
  solver=new Solver;
}

/*******************************************************************\

Function: satcheck_minisat1_prooft::satcheck_minisat1_prooft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1_prooft::satcheck_minisat1_prooft():satcheck_minisat1t()
{
  minisat_proof=new minisat_prooft;
  proof=new Proof(*minisat_proof);
  //  solver=new Solver;
  solver->proof=proof;
}

/*******************************************************************\

Function: satcheck_minisat1_prooft::~satcheck_minisat1_prooft

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1_prooft::~satcheck_minisat1_prooft()
{
  delete proof;
  delete minisat_proof;
}

/*******************************************************************\

Function: satcheck_minisat1_coret::satcheck_minisat1_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1_coret::satcheck_minisat1_coret()
{
}

/*******************************************************************\

Function: satcheck_minisat1_coret::~satcheck_minisat1_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1_coret::~satcheck_minisat1_coret()
{
}

/*******************************************************************\

Function: satcheck_minisat1_baset::~satcheck_minisat1_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_minisat1_baset::~satcheck_minisat1_baset()
{
  delete solver;
}

/*******************************************************************\

Function: satcheck_minisat1_prooft::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat1_prooft::solver_text()
{
  return "MiniSAT + Proof";
}

/*******************************************************************\

Function: satcheck_minisat1_coret::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_minisat1_coret::prop_solve()
{
  propt::resultt r;

  r=satcheck_minisat1_prooft::prop_solve();

  if(status==UNSAT)
  {
    in_core.resize(no_variables(), false);
    minisat_proof->resolution_proof.build_core(in_core);
  }

  return r;
}

/*******************************************************************\

Function: satcheck_minisat1_coret::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_minisat1_coret::solver_text()
{
  return "MiniSAT + Core";
}

/*******************************************************************\

Function: satcheck_minisat1_prooft::get_resolution_proof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

simple_prooft &satcheck_minisat1_prooft::get_resolution_proof()
{
  return minisat_proof->resolution_proof;
}
