/*******************************************************************\

Module: Test-Suite Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>
#include <util/xml.h>

#include <solvers/prop/cover_goals.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include "bmc.h"
#include "bv_cbmc.h"

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
  class basic_blockst
  {
  public:
    explicit basic_blockst(const goto_programt &_goto_program)
    {
      bool next_is_target=true;
      unsigned block_count=0;

      forall_goto_program_instructions(it, _goto_program)
      {
        if(next_is_target || it->is_target())
          block_count++;
          
        block_map[it]=block_count;
        
        next_is_target=
          it->is_goto() || it->is_return() ||
          it->is_function_call() || it->is_assume();
      }
    }
    
    typedef std::map<goto_programt::const_targett, unsigned> block_mapt;
    block_mapt block_map;
    
    inline unsigned operator[](goto_programt::const_targett t)
    {
      return block_map[t];
    }
  };

  bmc_covert(
    const goto_functionst &_goto_functions,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_bmc.prop_conv), bmc(_bmc)
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

  void collect_conditions(const exprt &src, std::set<exprt> &dest);
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
    
    // covered already?
    if(g.satisfied) continue;
  
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

Function: bmc_covert::collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_covert::collect_conditions(const exprt &src, std::set<exprt> &dest)
{
  if(src.id()==ID_and || src.id()==ID_or ||
     src.id()==ID_not || src.id()==ID_implies)
  {
    forall_operands(it, src)
      collect_conditions(*it, dest);
  }
  else if(src.is_true())
  {
  }
  else
  {
    dest.insert(src); 
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

  // we don't want the assertions to become constraints
  for(symex_target_equationt::SSA_stepst::iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end();
      it++)
    if(it->type==goto_trace_stept::ASSERT)
      it->type=goto_trace_stept::LOCATION;
  
  bmc.do_conversion();
  
  //bmc.equation.output(std::cout);
  
  std::map<goto_programt::const_targett, irep_idt> location_map;
  
  // Collect _all_ goals in `goal_map'.
  // This maps property IDs to 'goalt'
  forall_goto_functions(f_it, goto_functions)
  {
    basic_blockst basic_blocks(f_it->second.body);
  
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->function==ID__start ||
         i_it->function=="__CPROVER_initialize")
        continue;
        
      switch(criterion)
      {
      case C_ASSERTION:
        if(i_it->is_assert())
          goal_map[id(i_it)]=
            goalt(id2string(i_it->source_location.get_comment()));
        break;
        
      case C_LOCATION:
        {
          std::string b=i2string(basic_blocks[i_it]);
          std::string id=id2string(f_it->first)+"#"+b;
          location_map[i_it]=id;
          if(goal_map[id].description=="" &&
             i_it->source_location.get_file()!="")
            goal_map[id]=goalt("block "+i_it->source_location.as_string());
        }
        break;
      
      case C_BRANCH:
        if(i_it->is_goto() && !i_it->guard.is_true())
        {
          std::string b=i2string(basic_blocks[i_it]);
          goal_map[id(i_it, "TK")]=
            goalt("function "+id2string(f_it->first)+" block "+b+" branch taken");
          goal_map[id(i_it, "NT")]=
            goalt("function "+id2string(f_it->first)+" block "+b+" branch not taken");
        }
        break;
        
      case C_CONDITION:
        if(i_it->is_goto())
        {
          std::set<exprt> conditions;

          collect_conditions(i_it->guard, conditions);
          unsigned i=0;

          for(std::set<exprt>::const_iterator it=conditions.begin();
              it!=conditions.end();
              it++, i++)
          {
            goal_map[id(i_it, "C"+i2string(i))]=
              goalt("condition "+from_expr(bmc.ns, "", *it));
          }
        }
        break;
      
      default:;
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
      if(it->source.pc->is_assert())
        goal_map[id(it->source.pc)].add_instance(it, it->guard_literal);
      break;
      
    case C_LOCATION:
      {
        irep_idt id=location_map[it->source.pc];
        goal_map[id].add_instance(it, it->guard_literal);
      }
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
      xml_result.set_attribute("goal", id2string(it->first));
      xml_result.set_attribute("description", it->second.description);
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
           << cover_goals.iterations() << " iteration"
           << (cover_goals.iterations()==1?"":"s")
           << ")" << eom;
  
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
  const std::string &criterion)
{
  bmc_covert::criteriont c;
  
  if(criterion=="assertion" || criterion=="assertions")
    c=bmc_covert::C_ASSERTION;
  else if(criterion=="path" || criterion=="paths")
    c=bmc_covert::C_PATH;
  else if(criterion=="branch" || criterion=="branches")
    c=bmc_covert::C_BRANCH;
  else if(criterion=="location" || criterion=="locations")
    c=bmc_covert::C_LOCATION;
  else if(criterion=="decision" || criterion=="decisions")
    c=bmc_covert::C_DECISION;
  else if(criterion=="condition" || criterion=="conditions")
    c=bmc_covert::C_CONDITION;
  else if(criterion=="mcdc")
    c=bmc_covert::C_MCDC;
  else
  {
    error() << "coverage criterion `" << criterion << "' is unknown"
            << eom;
    return true;
  }

  bmc_covert bmc_cover(goto_functions, *this);
  bmc_cover.set_message_handler(get_message_handler());
  return bmc_cover(c);
}
