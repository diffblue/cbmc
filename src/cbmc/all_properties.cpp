/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>
#include <util/xml.h>
#include <util/json.h>

#include <solvers/sat/satcheck.h>
#include <solvers/prop/cover_goals.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>

#include "bmc.h"
#include "bv_cbmc.h"

/*******************************************************************\

   Class: bmc_all_propertiest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class bmc_all_propertiest:
  public cover_goalst::observert,
  public messaget
{
public:
  bmc_all_propertiest(
    const goto_functionst &_goto_functions,
    prop_convt &_solver,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_solver), bmc(_bmc)
  {
  }

  safety_checkert::resultt operator()();

  virtual void goal_covered(const cover_goalst::goalt &);

  struct goalt
  {
    // a property holds if all instances of it are true
    typedef std::vector<symex_target_equationt::SSA_stepst::iterator> instancest;
    instancest instances;
    std::string description;
    
    // if failed, we compute a goto_trace for the first failing instance
    enum statust { UNKNOWN, FAILURE, SUCCESS, ERROR } status;
    goto_tracet goto_trace;
    
    std::string status_string() const
    {
      switch(status)
      {
      case UNKNOWN: return "UNKNOWN";
      case FAILURE: return "FAILURE";
      case SUCCESS: return "SUCCESS";
      case ERROR: return "ERROR";
      }

      // make some poor compilers happy
      assert(false);
      return "";
    }
    
    explicit goalt(
      const goto_programt::instructiont &instruction):
      status(statust::UNKNOWN)
    {
      description=id2string(instruction.source_location.get_comment());
    }
    
    goalt():status(statust::UNKNOWN)
    {
    }
    
    exprt as_expr() const
    {
      std::vector<exprt> tmp;
      for(instancest::const_iterator
          it=instances.begin();
          it!=instances.end();
          it++)
        tmp.push_back(literal_exprt((*it)->cond_literal));
      return conjunction(tmp);
    }
  };

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

protected:
  const goto_functionst &goto_functions;
  prop_convt &solver;
  bmct &bmc;
};

/*******************************************************************\

Function: bmc_all_propertiest::goal_covered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_all_propertiest::goal_covered(const cover_goalst::goalt &)
{
  for(goal_mapt::iterator
      g_it=goal_map.begin();
      g_it!=goal_map.end();
      g_it++)
  {
    goalt &g=g_it->second;
    
    // failed already?
    if(g.status==goalt::statust::FAILURE) continue;
  
    // check whether failed
    for(goalt::instancest::const_iterator
        c_it=g.instances.begin();
        c_it!=g.instances.end();
        c_it++)
    {
      literalt cond=(*c_it)->cond_literal;
      
      if(solver.l_get(cond).is_false())
      {
        g.status=goalt::statust::FAILURE;
        symex_target_equationt::SSA_stepst::iterator next=*c_it;
        next++; // include the assertion
        build_goto_trace(bmc.equation, next, solver, bmc.ns, g.goto_trace);
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
  switch(bmc.ui)
  {
  case ui_message_handlert::PLAIN:
    {
      status() << "\n** Results:" << eom;
      for(const auto & it : goal_map)
        status() << "[" << it.first << "] "
                 << it.second.description << ": " << it.second.status_string()
                 << eom;

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
