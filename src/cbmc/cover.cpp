/*******************************************************************\

Module: Test-Suite Generation

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

#if 0
void bmct::cover(
  const goto_functionst &goto_functions,
  prop_convt &solver,
  const std::string &criterion)
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
#endif

/*******************************************************************\

   Class: bmc_covert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class bmc_covert:
  public cover_goalst::observert,
  public messaget
{
public:
  bmc_covert(
    const goto_functionst &_goto_functions,
    prop_convt &_solver,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_solver), bmc(_bmc)
  {
  }
  
  typedef enum { C_LOCATION, C_BRANCH, C_DECISION, C_CONDITION,
                 C_PATH, C_MCDC, C_ASSERTION } criteriont;

  const char *as_string(criteriont c)
  {
    switch(c)
    {
    case C_LOCATION: return "location";
    case C_BRANCH: return "branch";
    case C_DECISION: return "decision";
    case C_CONDITION: return "condition";
    case C_PATH: return "path";
    case C_MCDC: return "MC/DC";
    case C_ASSERTION: return "assertion";
    default: return "";
    }
  }

  bool operator()(const criteriont criterion);

  virtual void goal_covered(const cover_goalst::goalt &);

  struct goalt
  {
    // a criterion is satisfied if _any_ instance is true
    struct instancet
    {
      symex_target_equationt::SSA_stepst::iterator step;
      literalt condition;
    };
    
    typedef std::vector<instancet> instancest;
    instancest instances;
    
    void add_instance(
      symex_target_equationt::SSA_stepst::iterator step,
      literalt condition)
    {
      instances.push_back(instancet());
      instances.back().step=step;
      instances.back().condition=condition;
    }
    
    std::string description;
    
    // if satisified, we compute a goto_trace
    bool satisfied;
    goto_tracet goto_trace;
    
    explicit goalt(const std::string &_description):
      description(_description),
      satisfied(false)
    {
    }
    
    goalt():satisfied(false)
    {
    }
    
    exprt as_expr() const
    {
      std::vector<exprt> tmp;
      for(instancest::const_iterator
          it=instances.begin();
          it!=instances.end();
          it++)
        tmp.push_back(literal_exprt(it->condition));
      return conjunction(tmp);
    }
  };
  
  inline irep_idt id(
    goto_programt::const_targett loc,
    const std::string suffix="")
  {
    return id2string(loc->function)+
           "#"+i2string(loc->location_number)+
           suffix;
  }

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

protected:
  const goto_functionst &goto_functions;
  prop_convt &solver;
  bmct &bmc;
};

/*******************************************************************\

Function: bmc_covert::goal_covered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_covert::goal_covered(const cover_goalst::goalt &)
{
  for(goal_mapt::iterator
      g_it=goal_map.begin();
      g_it!=goal_map.end();
      g_it++)
  {
    goalt &g=g_it->second;
  
    // check whether satisfied
    for(goalt::instancest::const_iterator
        c_it=g.instances.begin();
        c_it!=g.instances.end();
        c_it++)
    {
      literalt cond=c_it->condition;
      
      if(solver.l_get(cond).is_true())
      {
        g.satisfied=true;
        symex_target_equationt::SSA_stepst::iterator next=c_it->step;
        next++; // include the instruction itself
        build_goto_trace(bmc.equation, next, solver, bmc.ns, g.goto_trace);
        break;
      }
    }
  }
}

/*******************************************************************\

Function: bmc_covert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmc_covert::operator()(const criteriont criterion)
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();
  
  bmc.do_conversion(solver);  
  
  // Collect _all_ goals in `goal_map'.
  // This maps property IDs to 'goalt'
  forall_goto_functions(f_it, goto_functions)
  {
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->function==ID__start ||
         i_it->function=="__CPROVER_initialize")
        continue;
        
      if(i_it->is_assert() ||
         i_it->is_assign() ||
         i_it->is_goto() ||
         i_it->is_end_function() ||
         i_it->is_decl() ||
         i_it->is_target())
      {        
        switch(criterion)
        {
        case C_ASSERTION:
          if(i_it->is_assert())
            goal_map[id(i_it)]=
              goalt(id2string(i_it->source_location.get_comment()));
          break;
          
        case C_LOCATION:
          goal_map[id(i_it)]=
            goalt("function "+id2string(f_it->first)+" location "+i2string(i_it->location_number));
          break;
        
        case C_BRANCH:
          if(i_it->is_goto() && !i_it->guard.is_true())
          {
            goal_map[id(i_it, "TK")]=
              goalt("function "+id2string(f_it->first)+" location "+i2string(i_it->location_number)+" branch taken");
            goal_map[id(i_it, "NT")]=
              goalt("function "+id2string(f_it->first)+" location "+i2string(i_it->location_number)+" branch not taken");
          }
          break;
        
        default:;
        }
      }
    }
  }

  // get the conditions for these goals from formula
  // collect all 'instances' of the goals
  for(symex_target_equationt::SSA_stepst::iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end();
      it++)
  {
    if(it->source.pc->function==ID__start ||
       it->source.pc->function=="__CPROVER_initialize")
      continue;

    switch(criterion)
    {
    case C_ASSERTION:
      if(it->is_assert() && it->source.pc->is_assert())
        goal_map[id(it->source.pc)].add_instance(it, it->cond_literal);
      break;
      
    case C_LOCATION:
      goal_map[id(it->source.pc)].add_instance(it, it->guard_literal);
      break;
    
    case C_BRANCH:
      if(it->is_goto() &&
         it->source.pc->is_goto() &&
         !it->source.pc->guard.is_true())
      {
        // a branch can have three states:
        // 1) taken 2) not taken 3) not executed!
        literalt bt=it->cond_literal;
        literalt bnt=solver.convert(and_exprt(
          literal_exprt(it->guard_literal), literal_exprt(!it->cond_literal)));

        goal_map[id(it->source.pc, "TK")].add_instance(it, bt);
        goal_map[id(it->source.pc, "NT")].add_instance(it, bnt);
      }
      break;
      
    default:;
    }
  }
  
  cover_goalst cover_goals(solver);
  
  cover_goals.register_observer(*this);
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    literalt l=solver.convert(it->second.as_expr());
    cover_goals.add(l);
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
    status() << "** " << as_string(criterion) << " coverage results:" << eom;
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
      xml_result.set_attribute("status", it->second.satisfied?"SATISFIED":"FAILED");

      if(it->second.satisfied)
        convert(bmc.ns, it->second.goto_trace, xml_result.new_element());

      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.description << ": " << (it->second.satisfied?"SATISFIED":"FAILED")
               << eom;
    }
  }

  status() << eom;
  
  status() << "** " << cover_goals.number_covered()
           << " of " << cover_goals.size() << " covered ("
           << cover_goals.iterations() << " iterations)" << eom;
  
  return false;
}

/*******************************************************************\

Function: bmct::cover

  Inputs:

 Outputs:

 Purpose: Try to cover all goals

\*******************************************************************/

bool bmct::cover(
  const goto_functionst &goto_functions,
  prop_convt &solver,
  const std::string &criterion)
{
  bmc_covert::criteriont c;
  
  if(criterion=="assertion")
    c=bmc_covert::C_ASSERTION;
  else if(criterion=="path")
    c=bmc_covert::C_PATH;
  else if(criterion=="branch")
    c=bmc_covert::C_BRANCH;
  else if(criterion=="location")
    c=bmc_covert::C_LOCATION;
  else if(criterion=="assertions")
    c=bmc_covert::C_DECISION;
  else if(criterion=="assertions")
    c=bmc_covert::C_CONDITION;
  else if(criterion=="mcdc")
    c=bmc_covert::C_MCDC;
  else
  {
    error() << "coverage criterion `" << criterion << "' is unknown"
            << eom;
    return true;
  }

  bmc_covert bmc_cover(goto_functions, solver, *this);
  bmc_cover.set_message_handler(get_message_handler());
  return bmc_cover(c);
}
