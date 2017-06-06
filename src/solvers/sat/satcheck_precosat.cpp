/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/


#include <cassert>

#include <util/threeval.h>

#include "satcheck_precosat.h"

#include <precosat.hh>

#ifndef HAVE_PRECOSAT
#error "Expected HAVE_PRECOSAT"
#endif

#define precosat_lit(a) ((a).var_no()*2 + !(a).sign())

tvt satcheck_precosatt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(a.var_no()>solver->getMaxVar())
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val=solver->val(precosat_lit(a));
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  return result;
}

const std::string satcheck_precosatt::solver_text()
{
  return "PrecoSAT";
}

void satcheck_precosatt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  forall_literals(it, new_bv)
    solver->add(precosat_lit(*it));

  solver->add(0);

  clause_counter++;
}

propt::resultt satcheck_precosatt::prop_solve()
{
  assert(status!=ERROR);

  // We start counting at 1, thus there is one variable fewer.
  {
    std::string msg=
      std::to_string(no_variables()-1)+" variables, "+
      std::to_string(solver->getAddedOrigClauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }

  std::string msg;

  const int res=solver->solve();
  if(res==1)
  {
    msg="SAT checker: instance is SATISFIABLE";
    messaget::status() << msg << messaget::eom;
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    assert(res==-1);
    msg="SAT checker: instance is UNSATISFIABLE";
    messaget::status() << msg << messaget::eom;
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

void satcheck_precosatt::set_assignment(literalt a, bool value)
{
  assert(false);
}

satcheck_precosatt::satcheck_precosatt() :
  solver(new PrecoSat::Solver())
{
  solver->init();
}

satcheck_precosatt::~satcheck_precosatt()
{
  delete solver;
}

/*
void satcheck_precosatt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  forall_literals(it, assumptions)
    assert(!it->is_constant());
}
*/
