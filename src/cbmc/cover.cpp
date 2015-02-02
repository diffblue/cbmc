/*******************************************************************\

Module: Vacuity Checks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/std_expr.h>

#include <solvers/sat/satcheck.h>
#include <solvers/prop/cover_goals.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

Function: bmct::cover_assertions

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

void bmct::cover_assertions(
  const goto_functionst &goto_functions,
  prop_convt &solver)
{
  // convert

  equation.convert_guards(solver);
  equation.convert_assignments(solver);
  equation.convert_decls(solver);
  equation.convert_assumptions(solver);

  // collect _all_ goals in `goal_map'
  typedef std::map<goto_programt::const_targett, exprt::operandst> goal_mapt;
  goal_mapt goal_map;
  
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it]=exprt::operandst();

  // get the conditions for these goals from formula

  exprt assumption=true_exprt();

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      // We just want reachability, i.e., the guard of the instruction,
      // not the assertion itself. The guard has been converted above.
      exprt goal=and_exprt(assumption, literal_exprt(it->guard_literal));

      goal_map[it->source.pc].push_back(goal);
    }
    else if(it->is_assume())
    {
      // Assumptions have been converted above.
      assumption=
        and_exprt(assumption, literal_exprt(it->cond_literal));
    }
  }
  
  // try to cover those
  cover_goalst cover_goals(solver);
  cover_goals.set_message_handler(get_message_handler());

  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // the following is FALSE if the bv is empty
    literalt condition=solver.convert(disjunction(it->second));
    cover_goals.add(condition);
  }

  status() << "Total number of coverage goals: " << cover_goals.size() << eom;

  cover_goals();

  // report
  std::list<cover_goalst::goalt>::const_iterator g_it=
    cover_goals.goals.begin();
      
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++, g_it++)
  {
    if(ui==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      
      // use this one
      xml_result.set_attribute("name", id2string(it->first->source_location.get_property_id()));

      xml_result.set_attribute("status",
        g_it->covered?"COVERED":"NOT_COVERED");
      
      std::cout << xml_result << "\n";
    }
    else
    {
      if(!g_it->covered)
        warning() << "!! failed to cover " << it->first->source_location;
    }
  }

  status() << eom;

  status() << "** Covered " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " in "
           << cover_goals.iterations() << " iterations" << eom;
}
