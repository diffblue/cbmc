/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck_minisat.h"

#include <algorithm>
#include <stack>

#include <util/invariant.h>
#include <util/threeval.h>

#include <Solver.h>
#include <Proof.h>

#ifndef HAVE_MINISAT
#error "Expected HAVE_MINISAT"
#endif

void convert(const bvt &bv, vec<Lit> &dest)
{
  dest.growTo(bv.size());

  for(unsigned i=0; i<bv.size(); i++)
    dest[i]=Lit(bv[i].var_no(), bv[i].sign());
}

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

void minisat_prooft::chain(const vec<ClauseId> &cs, const vec<Var> &xs)
{
  PRECONDITION(cs.size() == xs.size() + 1);

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
    INVARIANT(cs[i] < c_id, "clause ID should be within bounds");
    c.steps[i].clause_id=cs[i+1];
    c.steps[i].pivot_var_no=xs[i];
  }
}

tvt satcheck_minisat1_baset::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  INVARIANT(a.var_no() != 0, "variable number should be set");
  INVARIANT(
    a.var_no() < (unsigned)solver->model.size(),
    "variable number should be within bounds");

  if(solver->model[a.var_no()]==l_True)
    result=tvt(true);
  else if(solver->model[a.var_no()]==l_False)
    result=tvt(false);
  else
    result=tvt(tvt::tv_enumt::TV_UNKNOWN);

  if(a.sign())
    result=!result;

  return result;
}

const std::string satcheck_minisat1_baset::solver_text()
{
  return "MiniSAT 1.14p";
}

void satcheck_minisat1_baset::add_variables()
{
  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

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

  INVARIANT(
    std::all_of(
      new_bv.begin(),
      new_bv.end(),
      [](const literalt &l) { return l.var_no() < (unsigned)solver->nVars(); }),
    "variable number should be within bounds");

  solver->addClause(c);

  clause_counter++;
}

propt::resultt satcheck_minisat1_baset::prop_solve()
{
  PRECONDITION(status != ERROR);

  messaget::statistics() << (_no_variables - 1) << " variables, "
                         << solver->nClauses() << " clauses" << messaget::eom;

  add_variables();

  solver->simplifyDB();

  std::string msg;

  if(empty_clause_added)
  {
    msg="empty clause: instance is UNSATISFIABLE";
  }
  else if(!solver->okay())
  {
    msg="SAT checker inconsistent: instance is UNSATISFIABLE";
  }
  else
  {
    vec<Lit> MiniSat_assumptions;
    convert(assumptions, MiniSat_assumptions);

    if(solver->solve(MiniSat_assumptions))
    {
      msg="SAT checker: instance is SATISFIABLE";
      messaget::status() << msg << messaget::eom;
      status=SAT;
      return P_SATISFIABLE;
    }
    else
      msg="SAT checker: instance is UNSATISFIABLE";
  }

  messaget::status() << msg << messaget::eom;
  status=UNSAT;
  return P_UNSATISFIABLE;
}

void satcheck_minisat1_baset::set_assignment(literalt a, bool value)
{
  unsigned v=a.var_no();
  bool sign=a.sign();
  solver->model.growTo(v+1);
  value^=sign;
  solver->model[v]=lbool(value);
}

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

void satcheck_minisat1_baset::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  for(bvt::const_iterator it=assumptions.begin();
      it!=assumptions.end();
      it++)
    INVARIANT(!it->is_constant(), "assumptions should be non-constant");
}

satcheck_minisat1t::satcheck_minisat1t()
{
  empty_clause_added=false;
  solver=new Solver;
}

satcheck_minisat1_prooft::satcheck_minisat1_prooft():satcheck_minisat1t()
{
  minisat_proof=new minisat_prooft;
  proof=new Proof(*minisat_proof);
  //  solver=new Solver;
  solver->proof=proof;
}

satcheck_minisat1_prooft::~satcheck_minisat1_prooft()
{
  delete proof;
  delete minisat_proof;
}

satcheck_minisat1_coret::satcheck_minisat1_coret()
{
}

satcheck_minisat1_coret::~satcheck_minisat1_coret()
{
}

satcheck_minisat1_baset::~satcheck_minisat1_baset()
{
  delete solver;
}

const std::string satcheck_minisat1_prooft::solver_text()
{
  return "MiniSAT + Proof";
}

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

const std::string satcheck_minisat1_coret::solver_text()
{
  return "MiniSAT + Core";
}

simple_prooft &satcheck_minisat1_prooft::get_resolution_proof()
{
  return minisat_proof->resolution_proof;
}
