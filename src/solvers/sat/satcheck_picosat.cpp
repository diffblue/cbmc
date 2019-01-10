/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include "satcheck_picosat.h"

#include <algorithm>

#include <util/invariant.h>
#include <util/threeval.h>

extern "C"
{
#include <picosat.h>
}

#ifndef HAVE_PICOSAT
#error "Expected HAVE_PICOSAT"
#endif

tvt satcheck_picosatt::l_get(literalt a) const
{
  if(a.is_constant())
    return tvt(a.sign());

  tvt result;

  if(static_cast<int>(a.var_no())>picosat_variables(picosat))
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  const int val=picosat_deref(picosat, a.dimacs());
  if(val>0)
    result=tvt(true);
  else if(val<0)
    result=tvt(false);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);

  return result;
}

const std::string satcheck_picosatt::solver_text()
{
  return "PicoSAT";
}

void satcheck_picosatt::lcnf(const bvt &bv)
{
  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  picosat_adjust(picosat, _no_variables);

  forall_literals(it, new_bv)
    picosat_add(picosat, it->dimacs());

  picosat_add(picosat, 0);

  clause_counter++;
}

propt::resultt satcheck_picosatt::prop_solve()
{
  PRECONDITION(status != ERROR);

  {
    std::string msg=
      std::to_string(_no_variables-1)+" variables, "+
      std::to_string(picosat_added_original_clauses(picosat))+" clauses";
    messaget::statistics() << msg << messaget::eom;
  }

  std::string msg;

  forall_literals(it, assumptions)
    picosat_assume(picosat, it->dimacs());

  const int res=picosat_sat(picosat, -1);
  if(res==PICOSAT_SATISFIABLE)
  {
    msg="SAT checker: instance is SATISFIABLE";
    messaget::status() << msg << messaget::eom;
    status=SAT;
    return P_SATISFIABLE;
  }
  else
  {
    INVARIANT(
      res == PICOSAT_UNSATISFIABLE,
      "picosat result should report either sat or unsat");
    msg="SAT checker: instance is UNSATISFIABLE";
    messaget::status() << msg << messaget::eom;
  }

  status=UNSAT;
  return P_UNSATISFIABLE;
}

void satcheck_picosatt::set_assignment(literalt a, bool value)
{
  UNREACHABLE;
}

satcheck_picosatt::satcheck_picosatt()
{
  picosat = picosat_init();
}

satcheck_picosatt::~satcheck_picosatt()
{
  picosat_reset(picosat);
}

bool satcheck_picosatt::is_in_conflict(literalt a) const
{
  PRECONDITION(!a.is_constant());

  return picosat_failed_assumption(picosat, a.dimacs())!=0;
}

void satcheck_picosatt::set_assumptions(const bvt &bv)
{
  assumptions=bv;

  INVARIANT(
    std::all_of(
      assumptions.begin(),
      assumptions.end(),
      [](const literalt &l) { return !l.is_constant(); }),
    "assumptions should be non-constant");
}
