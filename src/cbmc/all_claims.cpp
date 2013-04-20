/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>

#include <solvers/sat/satcheck_minisat2.h>

#include <goto-symex/xml_goto_trace.h>

#include <solvers/prop/cover_goals.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

Function: bmct::all_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct goalt
{
  bvt bv;
  std::string description;

  explicit goalt(const goto_programt::instructiont &instruction)
  {
    description=id2string(instruction.location.get_comment());
  }
  
  goalt()
  {
  }
};

bool bmct::all_claims(const goto_functionst &goto_functions)
{
  satcheck_minisat_no_simplifiert satcheck;
  satcheck.set_message_handler(get_message_handler());
  satcheck.set_verbosity(get_verbosity());
  
  bv_cbmct bv_cbmc(ns, satcheck);
  
  if(options.get_option("arrays-uf")=="never")
    bv_cbmc.unbounded_array=bv_cbmct::U_NONE;
  else if(options.get_option("arrays-uf")=="always")
    bv_cbmc.unbounded_array=bv_cbmct::U_ALL;
    
  prop_convt &prop_conv=bv_cbmc;

  status("Passing problem to "+prop_conv.decision_procedure_text());

  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());

  // stop the time
  fine_timet sat_start=current_time();
  
  do_conversion(prop_conv);  
  
  // Collect _all_ goals in `goal_map'.
  // This maps claim IDs to 'goalt'
  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;
  
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it->location.get_claim()]=goalt(*i_it);

  // get the conditions for these goals from formula
  
  unsigned claim_counter=0;

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      irep_idt claim_id;

      if(it->source.pc->is_assert())
        claim_id=it->source.pc->location.get_claim();
      else
      {
        // need new claim ID, say for an unwinding assertion
        claim_counter++;
        claim_id=i2string(claim_counter);
        goal_map[claim_id].description=it->comment;
      }
      
      goal_map[claim_id].bv.push_back(it->cond_literal);
    }
  }
  
  cover_goalst cover_goals(prop_conv);
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // the following is TRUE if the bv is empty
    literalt p=prop_conv.prop.lnot(prop_conv.prop.land(it->second.bv));
    cover_goals.add(p);
  }

  status("Running "+prop_conv.decision_procedure_text());

  cover_goals();  

  // output runtime

  {
    std::ostringstream str;
    fine_timet sat_stop=current_time();

    str << "Runtime decision procedure: ";
    output_time(sat_stop-sat_start, str);
    str << "s";
    status(str.str());
  }
  
  // report
  if(ui!=ui_message_handlert::XML_UI)
  {
    status("");
    status("** Results:");
  }
  
  std::list<cover_goalst::cover_goalt>::const_iterator g_it=
    cover_goals.goals.begin();
    
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++, g_it++)
  {
    if(ui==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(it->first));

      xml_result.set_attribute("status",
        g_it->covered?"FAILURE":"SUCCESS");
    
      std::cout << xml_result << std::endl;
    }
    else
    {
      status(std::string("[")+id2string(it->first)+"] "+
             it->second.description+": "+(g_it->covered?"FAILED":"OK"));
    }
  }

  status("");
  
  status("** "+i2string(cover_goals.number_covered())+
         " of "+i2string(cover_goals.size())+" failed ("+
         i2string(cover_goals.iterations())+" iterations)");
  
  return false;
}

