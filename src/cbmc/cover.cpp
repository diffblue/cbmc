/*******************************************************************\

Module: Vacuity Checks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <solvers/sat/satcheck_minisat2.h>
#include <solvers/prop/cover_goals.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

Function: bmct::cover_assertions

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void bmct::cover_assertions(const goto_functionst &goto_functions)
{
  // with simplifier: need to freeze goal variables
  // to prevent them from being eliminated
  satcheck_minisat_no_simplifiert satcheck;
  
  satcheck.set_message_handler(get_message_handler());
  satcheck.set_verbosity(get_verbosity());
  
  bv_cbmct bv_cbmc(ns, satcheck);
  bv_cbmc.set_message_handler(get_message_handler());
  bv_cbmc.set_verbosity(get_verbosity());
  
  if(options.get_option("arrays-uf")=="never")
    bv_cbmc.unbounded_array=bv_cbmct::U_NONE;
  else if(options.get_option("arrays-uf")=="always")
    bv_cbmc.unbounded_array=bv_cbmct::U_ALL;

  prop_convt &prop_conv=bv_cbmc;

  // convert

  equation.convert_guards(prop_conv);
  equation.convert_assignments(prop_conv);
  equation.convert_decls(prop_conv);
  equation.convert_assumptions(prop_conv);

  // collect _all_ goals in `goal_map'
  typedef std::map<goto_programt::const_targett, bvt> goal_mapt;
  goal_mapt goal_map;
  
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it]=bvt();

  // get the conditions for these goals from formula

  literalt assumption_literal=const_literal(true);

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      // we just want reachability, i.e., the guard of the instruction,
      // not the assertion itself
      literalt l=
        prop_conv.prop.land(assumption_literal, it->guard_literal);

      goal_map[it->source.pc].push_back(l);
    }
    else if(it->is_assume())
      assumption_literal=
        prop_conv.prop.land(assumption_literal, it->cond_literal);
  }
  
  // try to cover those
  cover_goalst cover_goals(prop_conv);
  cover_goals.set_message_handler(get_message_handler());
  cover_goals.set_verbosity(get_verbosity());

  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // the following is FALSE if the bv is empty
    literalt condition=prop_conv.prop.lor(it->second);
    cover_goals.add(condition, it->first->location.as_string());
  }

  status("Total number of coverage goals: "+i2string(cover_goals.size()));

  cover_goals();

  // report
  for(std::list<cover_goalst::cover_goalt>::const_iterator
      g_it=cover_goals.goals.begin();
      g_it!=cover_goals.goals.end();
      g_it++)
    if(!g_it->covered)
    {
      warning("!! failed to cover "+g_it->description);
    }

  status("");
  status("** Covered "+i2string(cover_goals.number_covered())+
         " of "+i2string(cover_goals.size())+" in "+
         i2string(cover_goals.iterations())+" iterations");
}
