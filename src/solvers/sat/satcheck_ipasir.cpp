/*******************************************************************\

Module: External SAT Solver Binding

Author: Norbert Manthey, nmanthey@amazon.com

\*******************************************************************/

#include <algorithm>

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/threeval.h>

#include "satcheck_ipasir.h"

#ifdef HAVE_IPASIR

extern "C"
{
#include <ipasir.h>
}

/*

Interface description:
https://github.com/biotomas/ipasir/blob/master/ipasir.h

Representation:
Variables for a formula start with 1! 0 is used as termination symbol.

*/

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

const std::string satcheck_ipasirt::solver_text()
{
  return std::string(ipasir_signature());
}

void satcheck_ipasirt::lcnf(const bvt &bv)
{
  for(const auto &literal : bv)
  {
    if(literal.is_true())
      return;
    else if(!literal.is_false())
    {
      INVARIANT(
        literal.var_no() < (unsigned)no_variables(),
        "reject out of bound variables");
    }
  }

  for(const auto &literal : bv)
  {
    if(!literal.is_false())
    {
      // add literal with correct sign
      ipasir_add(solver, literal.dimacs());
    }
  }
  ipasir_add(solver, 0); // terminate clause

  if(solver_hardness)
  {
    // To map clauses to lines of program code, track clause indices in the
    // dimacs cnf output. Dimacs output is generated after processing
    // clauses to remove duplicates and clauses that are trivially true.
    // Here, a clause is checked to see if it can be thus eliminated. If
    // not, add the clause index to list of clauses in
    // solver_hardnesst::register_clause().
    static size_t cnf_clause_index = 0;
    bvt cnf;
    bool clause_removed = process_clause(bv, cnf);

    if(!clause_removed)
      cnf_clause_index++;

    solver_hardness->register_clause(
      bv, cnf, cnf_clause_index, !clause_removed);
  }

  clause_counter++;
}

propt::resultt satcheck_ipasirt::do_prop_solve()
{
  INVARIANT(status!=statust::ERROR, "there cannot be an error");

  log.statistics() << (no_variables() - 1) << " variables, " << clause_counter
                   << " clauses" << messaget::eom;

  // if assumptions contains false, we need this to be UNSAT
  bvt::const_iterator it =
    std::find_if(assumptions.begin(), assumptions.end(), is_false);
  const bool has_false = it != assumptions.end();

  if(has_false)
  {
    log.status() << "got FALSE as assumption: instance is UNSATISFIABLE"
                 << messaget::eom;
  }
  else
  {
    for(const auto &literal : assumptions)
    {
      if(!literal.is_false())
        ipasir_assume(solver, literal.dimacs());
    }

    // solve the formula, and handle the return code (10=SAT, 20=UNSAT)
    int solver_state = ipasir_solve(solver);
    if(10 == solver_state)
    {
      log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
      status = statust::SAT;
      return resultt::P_SATISFIABLE;
    }
    else if(20 == solver_state)
    {
      log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
    }
    else
    {
      log.status() << "SAT checker: solving returned without solution"
                   << messaget::eom;
      throw analysis_exceptiont(
        "solving inside IPASIR SAT solver has been interrupted");
    }
  }

  status=statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

void satcheck_ipasirt::set_assignment(literalt a, bool value)
{
  INVARIANT(!a.is_constant(), "cannot set an assignment for a constant");
  INVARIANT(false, "method not supported");
}

satcheck_ipasirt::satcheck_ipasirt(message_handlert &message_handler)
  : cnf_solvert(message_handler), solver(nullptr)
{
  INVARIANT(!solver, "there cannot be a solver already");
  solver=ipasir_init();
}

satcheck_ipasirt::~satcheck_ipasirt()
{
  if(solver)
    ipasir_release(solver);
  solver=nullptr;
}

bool satcheck_ipasirt::is_in_conflict(literalt a) const
{
  return ipasir_failed(solver, a.var_no());
}

void satcheck_ipasirt::set_assumptions(const bvt &bv)
{
  bvt::const_iterator it = std::find_if(bv.begin(), bv.end(), is_true);
  const bool has_true = it != bv.end();

  if(has_true)
  {
    assumptions.clear();
    return;
  }
  // only copy assertions, if there is no false in bt parameter
  assumptions=bv;
}

#endif
