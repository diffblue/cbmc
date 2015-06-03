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

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

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

  bool operator()();

  virtual void goal_covered(const cover_goalst::goalt &);

  struct goalt
  {
    // a property holds if all instances of it are true
    typedef std::vector<symex_target_equationt::SSA_stepst::iterator> instancest;
    instancest instances;
    std::string description;
    
    // if failed, we compute a goto_trace for the first failing instance
    bool failed;
    goto_tracet goto_trace;
    
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
  
    // check whether failed
    for(goalt::instancest::const_iterator
        c_it=g.instances.begin();
        c_it!=g.instances.end();
        c_it++)
    {
      literalt cond=(*c_it)->cond_literal;
      
      if(solver.l_get(cond).is_false())
      {
        g.failed=true;
        symex_target_equationt::SSA_stepst::iterator next=*c_it;
        next++; // include the assertion
        build_goto_trace(bmc.equation, next, solver, bmc.ns, g.goto_trace);
#if 0
        show_goto_trace(std::cout, bmc.ns, g.goto_trace);
#endif
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

bool bmc_all_propertiest::operator()()
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();
  
  bmc.do_conversion(solver);  
  
  // Collect _all_ goals in `goal_map'.
  // This maps claim IDs to 'goalt'
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it->source_location.get_property_id()]=goalt(*i_it);

  // get the conditions for these goals from formula
  
  unsigned property_counter=0;

  // collect all 'instances' of the properties
  for(symex_target_equationt::SSA_stepst::iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert() &&
       it->comment!="loop_condition_check")
    {
      irep_idt property_id;

      if(it->source.pc->is_assert())
        property_id=it->source.pc->source_location.get_property_id();
      else
      {
        // need new property ID, say for an unwinding assertion
        property_counter++;
        property_id=i2string(property_counter);
        goal_map[property_id].description=it->comment;
      }
      
      //need to convert again as the context of the expression 
      //  may have changed
      it->cond_literal = solver.convert(it->cond_expr);
      goal_map[property_id].instances.push_back(it);
    }
  }
  
  cover_goalst cover_goals(solver);

  //set activation literal for incremental checking
  cover_goals.activation_literal = bmc.equation.current_activation_literal();

#if 0
  std::cout << "cover_goals.activation_literal = " << cover_goals.activation_literal << std::endl;
#endif

  cover_goals.register_observer(*this);
  
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

  solver.set_assumptions(bmc.equation.activate_assertions);
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
  
  bool res = true;

  for(goal_mapt::iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    if(!it->second.failed) res = false;
    if(bmc.ui==ui_message_handlert::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(it->first));
      xml_result.set_attribute("status", it->second.failed?"FAILURE":"SUCCESS");

      if(it->second.failed)
        convert(bmc.ns, it->second.goto_trace, xml_result.new_element());

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

  return res;
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
  bmc_all_propertiest bmc_all_properties(goto_functions, solver, *this);
  bmc_all_properties.set_message_handler(get_message_handler());
  return bmc_all_properties();
}
