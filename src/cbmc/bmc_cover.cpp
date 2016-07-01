/*******************************************************************\

Module: Test-Suite Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/time_stopping.h>
#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/json.h>
#include <util/json_expr.h>

#include <solvers/prop/cover_goals.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>

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
    
    void output(std::ostream &out)
    {
      for(const auto &b_it : block_map)
        out << b_it.first->source_location
            << " -> " << b_it.second
            << '\n';
    }
  };

  bmc_covert(
    const goto_functionst &_goto_functions,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_bmc.prop_conv), bmc(_bmc)
  {
  }
  
  bool operator()();

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
    source_locationt source_location;
    
    // if satisified, we compute a goto_trace
    bool satisfied;
    goto_tracet goto_trace;
    
    goalt(
      const std::string &_description,
      const source_locationt &_source_location):
      description(_description),
      source_location(_source_location),
      satisfied(false)
    {
    }
    
    goalt():source_location(source_locationt::nil()),
            satisfied(false)
    {
    }
    
    exprt as_expr() const
    {
      std::vector<exprt> tmp;

      for(const auto &it : instances)
        tmp.push_back(literal_exprt(it.condition));

      return disjunction(tmp);
    }
  };
  
  inline irep_idt id(goto_programt::const_targett loc)
  {
    return loc->source_location.get_property_id();
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
  for(auto &g_it : goal_map)
  {
    goalt &g=g_it.second;
    
    // covered already?
    if(g.satisfied) continue;
  
    // check whether satisfied
    for(const auto &c_it : g.instances)
    {
      literalt cond=c_it.condition;
      
      if(solver.l_get(cond).is_true())
      {
        status() << "Covered " << g.description << messaget::eom;
        g.satisfied=true;
        symex_target_equationt::SSA_stepst::iterator next=c_it.step;
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

bool bmc_covert::operator()()
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();

  // Collect _all_ goals in `goal_map'.
  // This maps property IDs to 'goalt'
  forall_goto_functions(f_it, goto_functions)
  {
    basic_blockst basic_blocks(f_it->second.body);
    
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert())
        goal_map[id(i_it)]=
          goalt(
            id2string(i_it->source_location.get_comment()),
            i_it->source_location);
    }
  }

  for(auto & it : bmc.equation.SSA_steps)
    it.cond_literal=literalt(0, 0);
  
  // Do conversion to next solver layer
  
  bmc.do_conversion();
  
  //bmc.equation.output(std::cout);
  
  // get the conditions for these goals from formula
  // collect all 'instances' of the goals
  for(auto it = bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      assert(it->source.pc->is_assert());
      exprt c=
        conjunction({
          literal_exprt(it->guard_literal),
          literal_exprt(!it->cond_literal) });
      literalt l_c=solver.convert(c);
      goal_map[id(it->source.pc)].add_instance(it, l_c);
    }
  }
  
  status() << "Aiming to cover " << goal_map.size() << " goal(s)" << eom;
  
  cover_goalst cover_goals(solver);
  
  cover_goals.register_observer(*this);
  
  for(const auto &it : goal_map)
  {
    literalt l=solver.convert(it.second.as_expr());
    cover_goals.add(l);
  }
  
  assert(cover_goals.size()==goal_map.size());

  status() << "Running " << solver.decision_procedure_text() << eom;

  cover_goals();  

  // output runtime

  {
    absolute_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }
  
  // report
  unsigned goals_covered=0;
  switch(bmc.ui)
  {
    case ui_message_handlert::PLAIN:
    {
      status() << "\n** coverage results:" << eom;

      for(const auto & it : goal_map)
      {
        const goalt &goal=it.second;

        if(goal.satisfied) goals_covered++;

        status() << "[" << it.first << "]";

        if(goal.source_location.is_not_nil())
          status() << ' ' << goal.source_location;

        if(!goal.description.empty()) status() << ' ' << goal.description;

        status() << ": " << (goal.satisfied?"SATISFIED":"FAILED")
                 << eom;
      }

      status() << '\n';

      break;
    }
    case ui_message_handlert::XML_UI:
    {
      for(const auto & it : goal_map)
      {
        const goalt &goal=it.second;

        if(goal.satisfied) goals_covered++;

        xmlt xml_result("result");
        xml_result.set_attribute("goal", id2string(it.first));
        xml_result.set_attribute("description", goal.description);
        xml_result.set_attribute("status", goal.satisfied?"SATISFIED":"FAILED");

        if(goal.source_location.is_not_nil())
          xml_result.new_element()=xml(goal.source_location);

        if(goal.satisfied)
          convert(bmc.ns, goal.goto_trace, xml_result.new_element());

        std::cout << xml_result << "\n";
      }

      break;
    }
    case ui_message_handlert::JSON_UI:
    {
      json_objectt json_result;
      json_arrayt &result_array=json_result["results"].make_array();
      for(const auto & it : goal_map)
      {
        const goalt &goal=it.second;

        if(goal.satisfied) goals_covered++;

        json_objectt &result=result_array.push_back().make_object();
        result["status"]=json_stringt(goal.satisfied?"satisfied":"failed");
        result["goal"]=json_stringt(id2string(it.first));
        result["description"]=json_stringt(goal.description);

        if(goal.source_location.is_not_nil())
          result["sourceLocation"]=json(goal.source_location);

        if(goal.satisfied)
        {
          jsont &json_trace=result["trace"];
          convert(bmc.ns, goal.goto_trace, json_trace);
        }
      }
      json_result["totalGoals"]=json_numbert(i2string(goal_map.size()));
      json_result["goalsCovered"]=json_numbert(i2string(goals_covered));
      std::cout << ",\n" << json_result;
      break;
    }
  }

  status() << "** " << goals_covered
           << " of " << goal_map.size() << " covered ("
           << std::fixed << std::setw(1) << std::setprecision(1)
           << (goal_map.empty()?100.0:100.0*goals_covered/goal_map.size())
           << "%), using "
           << cover_goals.iterations() << " iteration"
           << (cover_goals.iterations()==1?"":"s")
           << eom;
  
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
  bmc_covert bmc_cover(goto_functions, *this);
  bmc_cover.set_message_handler(get_message_handler());
  return bmc_cover();
}
