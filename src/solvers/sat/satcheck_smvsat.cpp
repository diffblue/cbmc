/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <stack>


#include "satcheck_smvsat.h"

#include <satsolvercore.h>
#include <interpolator.h>

satcheck_smvsatt::satcheck_smvsatt()
{
  satsolver=
    sat_instance_new_type(SATSOLVERCORE1, no_variables(), true);

  // now we can do l_const
  init_const();
}

satcheck_smvsat_coret::satcheck_smvsat_coret()
{
}

satcheck_smvsatt::~satcheck_smvsatt()
{
}

tvt satcheck_smvsatt::l_get(literalt a) const
{
  assert(status==SAT);

  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;
  unsigned v=a.var_no();

  switch(sat_instance_value(satsolver, v))
  {
    case 0: result=tvt(false); break;
    case 1: result=tvt(true); break;
    default: result=tvt(tvt::tv_enumt::TV_UNKNOWN); break;
  }

  if(a.sign())
    result=!result;

  return result;
}

const std::string satcheck_smvsatt::solver_text()
{
  return std::string("SMVSAT");
}

void satcheck_smvsatt::lcnf(const bvt &bv)
{
  bvt tmp;

  if(process_clause(bv, tmp))
    return;

  int *lits=new int[tmp.size()+1];

  for(unsigned i=0; i<tmp.size(); i++)
    lits[i]=tmp[i].dimacs();

  // zero-terminated
  lits[tmp.size()]=0;

  sat_instance_add_clause(satsolver, lits);

  clause_counter++;

  delete[] lits;
}

propt::resultt satcheck_smvsatt::prop_solve()
{
  int result=sat_instance_solve(satsolver);

  {
    std::string msg;

    switch(result)
    {
    case 0:
      msg="SAT checker: instance is UNSATISFIABLE";
      break;

    case 1:
      msg="SAT checker: instance is SATISFIABLE";
      break;

    default:
      msg="SAT checker failed: unknown result";
      break;
    }

    messaget::status() << msg << messaget::eom;
  }

  if(result==0)
  {
    status=UNSAT;
    return P_UNSATISFIABLE;
  }

  if(result==1)
  {
    status=SAT;
    return P_SATISFIABLE;
  }

  status=ERROR;

  return P_ERROR;
}

propt::resultt satcheck_smvsat_coret::prop_solve()
{
  propt::resultt result=satcheck_smvsatt::prop_solve();

  if(result==P_UNSATISFIABLE)
  {
    // TODO
  }

  return result;
}

void satcheck_smvsat_interpolatort::lcnf(const bvt &bv)
{
  bvt tmp;

  if(process_clause(bv, tmp))
    return;

  int *lits=new int[tmp.size()+1];

  for(unsigned i=0; i<tmp.size(); i++)
    lits[i]=tmp[i].dimacs();

  // zero-terminated
  lits[tmp.size()]=0;

  unsigned clause_id=sat_instance_add_clause(satsolver, lits);

  if(partition_numbers.size()<=clause_id)
    partition_numbers.resize(clause_id+1, -1);

  partition_numbers[clause_id]=partition_no;

  delete[] lits;
}

void satcheck_smvsat_interpolatort::interpolate(exprt &dest)
{
  // crate instance

  // NOLINTNEXTLINE(readability/identifiers)
  struct interpolator *interpolator_satsolver=
    new_interpolator(satsolver);

  // set partition numbers

  for(unsigned i=0; i<partition_numbers.size(); i++)
  {
    short p=partition_numbers[i];
    if(p!=-1)
      interpolator_satsolver->set_clause_partition(i, p);
  }

  int output=interpolator_satsolver->interpolate(0, 0);

  build_aig(*interpolator_satsolver, output, dest);

  delete interpolator_satsolver;
}

void satcheck_smvsat_interpolatort::build_aig(
  // NOLINTNEXTLINE(readability/identifiers)
  struct interpolator &interpolator_satsolver,
  int output,
  exprt &dest)
{
  std::stack<entryt> stack;

  stack.push(entryt(output, &dest));

  while(!stack.empty())
  {
    entryt x=stack.top();
    stack.pop();

    bool invert=x.g<0;
    int n=invert?-x.g:x.g;

    assert(n!=0);

    exprt &e=*x.e;

    if(n==INT_MAX)
      e.make_true();
    else if(n<=satsolver->num_variables())
    { // a SAT variable
      e.id(ID_symbol);
      e.set(ID_identifier, n);
    }
    else
    {
      e.id(ID_and);
      e.operands().resize(2);

      unsigned g0=interpolator_satsolver.aig_arg(n, 0);
      unsigned g1=interpolator_satsolver.aig_arg(n, 1);

      stack.push(entryt(g0, &e.op0()));
      stack.push(entryt(g1, &e.op1()));
    }

    if(invert)
      e.make_not();
  }
}
