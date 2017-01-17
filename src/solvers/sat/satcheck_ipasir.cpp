/*******************************************************************\

Module:

Author: Norbert Manthey, nmanthey@amazon.com

\*******************************************************************/

#ifndef _MSC_VER
#include <inttypes.h>
#endif

#include <cassert>
#include <stack>

#include <util/threeval.h>

#include "satcheck_ipasir.h"

extern "C"
{
#include <ipasir.h>
}

#ifndef HAVE_IPASIR
#error "Expected HAVE_IPASIR"
#endif

/* solver interface:

Representation:
Variables for a formula start with 1! 0 is used as termination symbol.

Functions:
const char * ipasir_signature ();
void * ipasir_init ();
void ipasir_release (void * solver);
void ipasir_add (void * solver, int lit_or_zero);
void ipasir_assume (void * solver, int lit);
int ipasir_solve (void * solver);
int ipasir_val (void * solver, int lit);
int ipasir_failed (void * solver, int lit);
void ipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state));

*/

/*******************************************************************\

Function: satcheck_ipasirt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


tvt satcheck_ipasirt::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  // compare to internal no_variables number
  if(a.var_no()>=(unsigned)no_variables())
    return tvt::unknown();

  const int val=ipasir_val(solver, a.var_no());

  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt::unknown();

  if(a.sign())
    result=!result;

  return result;
}

/*******************************************************************\

Function: satcheck_minisat_no_simplifiert::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_ipasirt::solver_text()
{
  return std::string(ipasir_signature());
}

/*******************************************************************\

Function: satcheck_ipasirt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void satcheck_ipasirt::lcnf(const bvt &bv)
{
  forall_literals(it, bv)
  {
    if(it->is_true())
      return;
    else if(!it->is_false())
      assert(it->var_no()<(unsigned)no_variables());
  }


  forall_literals(it, bv)
  {
    if(!it->is_false())
    {
      // add literal wit correct sign
      ipasir_add(solver, it->sign()?-it->var_no():it->var_no());
    }
  }
  ipasir_add(solver, 0); // terminate clause

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_ipasirt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


propt::resultt satcheck_ipasirt::prop_solve()
{
  assert(status!=ERROR);

  {
    messaget::status() <<
      (no_variables()-1) << " variables, " <<
      clause_counter << " clauses" << eom;
  }

    // use the internal representation, as ipasir does not support reporting the
    // status
    if(status==UNSAT)
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
        forall_literals(it, assumptions)
          if(!it->is_false())
            ipasir_assume(solver, it->sign()?-it->var_no():it->var_no());

        if(10==ipasir_solve(solver))
        {
          messaget::status() <<
            "SAT checker: instance is SATISFIABLE" << eom;
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

Function: satcheck_ipasirt::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void satcheck_ipasirt::set_assignment(literalt a, bool value)
{
  assert(!a.is_constant());
  assert(false && "method not supported");
}

/*******************************************************************\

Function: satcheck_ipasirt::satcheck_ipasirt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


satcheck_ipasirt::satcheck_ipasirt()
: solver(0)
{
  assert(!solver);
  solver=ipasir_init();
}

/*******************************************************************\

Function: satcheck_ipasirt::~satcheck_ipasirt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_ipasirt::~satcheck_ipasirt()
{
  if(solver)
    ipasir_release(solver);
  solver=0;
}

/*******************************************************************\

Function: satcheck_ipasirt::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


bool satcheck_ipasirt::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  if(ipasir_failed(solver, v))
      return true;
  return false;
}

/*******************************************************************\

Function: satcheck_ipasirt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/


void satcheck_ipasirt::set_assumptions(const bvt &bv)
{
  forall_literals(it, bv)
    if(it->is_true())
    {
      assumptions.clear();
      return;
    }
  // only copy assertions, if there is no false in bt parameter
  assumptions=bv;
}
