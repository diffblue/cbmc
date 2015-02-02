/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>
#include <util/xml.h>

#include <solvers/sat/satcheck.h>
#include <solvers/prop/cover_goals.h>
#include <solvers/prop/literal_expr.h>

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
  bool operator()(
    const goto_functionst &goto_functions,
    prop_convt &solver,
    bmct &bmc);

  virtual void goal_covered(const cover_goalst::goalt &);

  struct goalt
  {
    // a property holds if all instances of it are true
    std::vector<literalt> conjuncts;
    std::string description;
    bool failed;
    
    explicit goalt(
      const goto_programt::instructiont &instruction):
      failed(false)
    {
      description=id2string(instruction.source_location.get_comment());
    }
    
    goalt():failed(false)
    {
    }
    
    exprt as_expr() const
    {
      std::vector<exprt> tmp;
      for(std::vector<literalt>::const_iterator
          it=conjuncts.begin();
          it!=conjuncts.end();
          it++)
        tmp.push_back(literal_exprt(*it));
      return conjunction(tmp);
    }
  };

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;
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
  
    // check whether failed
    for(std::vector<literalt>::const_iterator
        c_it=g.conjuncts.begin();
        c_it!=g.conjuncts.end();
        c_it++)
    {
    }
  }
}

/*******************************************************************\

Function: bmc_all_propertiest::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_all_propertiest::operator()(
  const goto_functionst &goto_functions,
  prop_convt &solver,
  bmct &bmc)
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();
  
  bmc.do_conversion(solver);  
  
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
        property_id=id2string(it->source.pc->source_location.get_function())+".unwind."+
                    i2string(it->source.pc->loop_number);
        goal_map[property_id].description=it->comment;
      }
      else
        continue;
      
      goal_map[property_id].conjuncts.push_back(it->cond_literal);
    }
  }
  
  cover_goalst cover_goals(solver);
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    literalt p=!solver.convert(it->second.as_expr());
    cover_goals.add(p);
  }

  status() << "Running " << solver.decision_procedure_text() << eom;

  cover_goals();  

  // output runtime

  {
    absolute_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }
  
  // report
  if(bmc.ui!=ui_message_handlert::XML_UI)
  {
    status() << eom;
    status() << "** Results:" << eom;
  }
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    if(bmc.ui==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(it->first));
      xml_result.set_attribute("status", it->second.failed?"FAILURE":"SUCCESS");
      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.description << ": " << (it->second.failed?"FAILED":"OK")
               << eom;
    }
  }

  status() << eom;
  
  status() << "** " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " failed ("
           << cover_goals.iterations() << " iterations)" << eom;
  
  return false;
}

/*******************************************************************\

Function: bmct::all_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::all_properties(
  const goto_functionst &goto_functions,
  prop_convt &solver)
{
  bmc_all_propertiest bmc_all_properties;
  bmc_all_properties.set_message_handler(get_message_handler());
  return bmc_all_properties(goto_functions, solver, *this);
}
