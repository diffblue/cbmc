/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>
#include <util/xml.h>
#include <util/json.h>

#include <solvers/sat/satcheck.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>

#include "bv_cbmc.h"

#include "all_properties_class.h"

/*******************************************************************\

Function: bmc_all_propertiest::goal_covered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_all_propertiest::goal_covered(const cover_goalst::goalt &)
{
  for(auto &g : goal_map)
  {
    // failed already?
    if(g.second.status==goalt::statust::FAILURE) continue;
  
    // check whether failed
    for(auto &c : g.second.instances)
    {
      literalt cond=c->cond_literal;
      
      if(solver.l_get(cond).is_false())
      {
        g.second.status=goalt::statust::FAILURE;
        symex_target_equationt::SSA_stepst::iterator next=c;
        next++; // include the assertion
        build_goto_trace(bmc.equation, next, solver, bmc.ns, 
                         g.second.goto_trace);
        break;
      }
    }
  }
}

/*******************************************************************\

Function: bmc_all_propertiest::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt bmc_all_propertiest::operator()()
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();
  
  bmc.do_conversion();  
  
  // Collect _all_ goals in `goal_map'.
  // This maps property IDs to 'goalt'
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it->source_location.get_property_id()]=goalt(*i_it);

  // get the conditions for these goals from formula
  // collect all 'instances' of the properties
  for(symex_target_equationt::SSA_stepst::iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      irep_idt property_id;

      if(it->source.pc->is_assert())
        property_id=it->source.pc->source_location.get_property_id();
      else if(it->source.pc->is_goto())
      {
        // this is likely an unwinding assertion
        property_id=id2string(
          it->source.pc->source_location.get_function())+".unwind."+
          i2string(it->source.pc->loop_number);
        goal_map[property_id].description=it->comment;
      }
      else
        continue;
      
      goal_map[property_id].instances.push_back(it);
    }
  }
  
  do_before_solving();

  cover_goalst cover_goals(solver);

  cover_goals.set_message_handler(get_message_handler());  
  cover_goals.register_observer(*this);
  
  for(const auto & g : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    literalt p=!solver.convert(g.second.as_expr());
    cover_goals.add(p);
  }

  status() << "Running " << solver.decision_procedure_text() << eom;

  bool error=false;
  
  decision_proceduret::resultt result=cover_goals();

  if(result==decision_proceduret::D_ERROR)
  {
    error=true;
    for(auto & g : goal_map)
      if(g.second.status==goalt::statust::UNKNOWN)
        g.second.status=goalt::statust::ERROR;
  }
  else
  {
    for(auto & g : goal_map)
      if(g.second.status==goalt::statust::UNKNOWN)
        g.second.status=goalt::statust::SUCCESS;
  }

  // output runtime

  {
    absolute_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }
  
  // report
  report(cover_goals);

  if(error)
    return safety_checkert::ERROR;

  bool safe=(cover_goals.number_covered()==0);

  if(safe)
    bmc.report_success(); // legacy, might go away
  else
    bmc.report_failure(); // legacy, might go away
  
  return safe?safety_checkert::SAFE:safety_checkert::UNSAFE;
}

/*******************************************************************\

Function: bmc_all_propertiest::report()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_all_propertiest::report(const cover_goalst &cover_goals)
{
  switch(bmc.ui)
  {
  case ui_message_handlert::PLAIN:
    {
      status() << "\n** Results:" << eom;

      for(const auto & it : goal_map)
        status() << "[" << it.first << "] "
                 << it.second.description << ": " << it.second.status_string()
                 << eom;

      if(bmc.options.get_bool_option("trace"))
        for(const auto & it : goal_map)
          if(it.second.status==goalt::statust::FAILURE)
          {
            std::cout << "\n" << "Trace for " << it.first << ":" << "\n";
            show_goto_trace(std::cout, bmc.ns, it.second.goto_trace);
          }

      status() << "\n** " << cover_goals.number_covered()
               << " of " << cover_goals.size() << " failed ("
               << cover_goals.iterations() << " iteration"
               << (cover_goals.iterations()==1?"":"s")
               << ")" << eom;
    }
    break;

  case ui_message_handlert::XML_UI:
    {
      for(const auto & it : goal_map)
      {
        xmlt xml_result("result");
        xml_result.set_attribute("property", id2string(it.first));
        xml_result.set_attribute("status", it.second.status_string());

        if(it.second.status==goalt::statust::FAILURE)
          convert(bmc.ns, it.second.goto_trace, xml_result.new_element());

        std::cout << xml_result << "\n";
      }
      break;
    }

    case ui_message_handlert::JSON_UI:
    {
      json_objectt json_result;
      json_arrayt &result_array=json_result["result"].make_array();

      for(const auto & it : goal_map)
      {
        json_objectt &result=result_array.push_back().make_object();
        result["property"]=json_stringt(id2string(it.first));
        result["description"]=json_stringt(id2string(it.second.description));
        result["status"]=json_stringt(it.second.status_string());

        if(it.second.status==goalt::statust::FAILURE)
        {
          jsont &json_trace=result["trace"];
          convert(bmc.ns, it.second.goto_trace, json_trace);
        }
      }

      std::cout << ",\n" << json_result;
    }
    break;

  }
}

/*******************************************************************\

Function: bmct::all_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt bmct::all_properties(
  const goto_functionst &goto_functions,
  prop_convt &solver)
{
  bmc_all_propertiest bmc_all_properties(goto_functions, solver, *this);
  bmc_all_properties.set_message_handler(get_message_handler());
  return bmc_all_properties();
}
