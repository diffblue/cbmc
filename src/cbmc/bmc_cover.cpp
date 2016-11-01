/*******************************************************************\

Module: Test-Suite Generation with BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <iostream>
#include <algorithm>

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
  bmc_covert(
    const goto_functionst &_goto_functions,
    bmct &_bmc):
    goto_functions(_goto_functions), solver(_bmc.prop_conv), bmc(_bmc)
  {
  }
  
  bool operator()();

  // gets called by prop_covert
  virtual void satisfying_assignment();

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

  struct testt
  {
    goto_tracet goto_trace;
    std::set<irep_idt> covered_goals;
    std::string source_code;
    std::string test_function_name;
  };
  
  inline irep_idt id(goto_programt::const_targett loc)
  {
    return loc->source_location.get_property_id();
  }

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;
  typedef std::vector<testt> testst;
  testst tests;


  static void print_testsuite(const testst &tests) 
  {
    int i=1;
    for(auto &test : tests)
    {
      std::cout << "Goals in test " << i << " : " << std::endl;
      for (auto &goal : test.covered_goals)
        std::cout << id2string(goal) << ";";

      std::cout << std::endl;
      i++;
    }
  }
  
// compute covered goals set difference
  static void goals_diff(std::set<irep_idt> &goals1, 
			 const std::set<irep_idt> &goals2) 
  {
    std::set<irep_idt>::iterator it1=goals1.begin();
    std::set<irep_idt>::iterator it2=goals2.begin();
    while (it1!=goals1.end() && it2!=goals2.end()) 
    {
      if (*it1<*it2) ++it1;
      else if (*it2<*it1) ++it2;
      else 
      {
        ++it2;
        it1=goals1.erase(it1);
      }
    }
  }
  
  static bool compare_tests(testt x,testt y) 
  {
    return x.covered_goals.size()>y.covered_goals.size(); 
  }

// greedy n^2 algorithm by descending ordering
  void minimise_testsuite(testst& tsi, const unsigned no_goals) 
  {
    testst tss;
    unsigned no_covered=0;
    std::vector<irep_idt> goals;
    goals.clear();

    int initial_size=tsi.size();
    tss=tsi;
    tsi.clear(); // this is where we'll next collect the minimised testsuite

    while(!tss.empty()) 
    {
      std::sort(tss.begin(), tss.end(), compare_tests); // descending order of remaining test cases
      testt tc=*tss.begin(); // pick the first test 
      if(tc.covered_goals.empty()) break; // break if it does not contribute (and so do the remaining ones)
      tss.erase(tss.begin()); // remove test case on top
      tsi.push_back(tc); // add it to the output suite 
      no_covered+=tc.covered_goals.size();
      if(no_covered==no_goals)
        break; // we've covered all the goals
      for(auto &it : tss)
      {
        if(it.covered_goals.empty()) break; // break if remaining test cases will not contribute anyway
        goals_diff(it.covered_goals, tc.covered_goals); // remove goals that are covered by the picked one
      }    
    }

    status() << "Reduced from " << initial_size << " to " 
	     << tsi.size() << " test cases " << messaget::eom;

  }
  
  std::string get_test(const goto_tracet &goto_trace) const
  {
    bool first=true;
    std::string test;
    for(const auto & step : goto_trace.steps)
    {
      if(step.is_input())
      {
        if(first)
          first=false;
        else
          test+=", ";

        test+=id2string(step.io_id)+"=";

        if(step.io_args.size()==1)
          test+=from_expr(bmc.ns, "", step.io_args.front());
      }
    }
    return test;
  }

protected:
  const goto_functionst &goto_functions;
  prop_convt &solver;
  bmct &bmc;
};

/*******************************************************************\

Function: bmc_covert::satisfying_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_covert::satisfying_assignment()
{
  tests.push_back(testt());
  testt &test = tests.back();

  for(auto &g_it : goal_map)
  {
    goalt &g=g_it.second;
    
#if 0 // removed the filtering of already covered goals as we need the list
    // of all covered goals for subsequent testsuite minimisation.

    // covered already?
    if(g.satisfied) continue;
#endif
  
    // check whether satisfied
    for(const auto &c_it : g.instances)
    {
      literalt cond=c_it.condition;
      
      if(solver.l_get(cond).is_true())
      {
        status() << "Covered " << g.description << messaget::eom;
        g.satisfied=true;
        test.covered_goals.insert(g_it.first);
        break;
      }
    }
  }

  build_goto_trace(bmc.equation, bmc.equation.SSA_steps.end(), 
                   solver, bmc.ns, test.goto_trace);

  goto_tracet &goto_trace=test.goto_trace;

  // Now delete anything after first failed assumption
  for(goto_tracet::stepst::iterator
      s_it1=goto_trace.steps.begin();
      s_it1!=goto_trace.steps.end();
      s_it1++)
    if(s_it1->is_assume() && !s_it1->cond_value)
    {
      s_it1++;

      for(goto_tracet::stepst::iterator
          s_it2=s_it1;
          s_it2!=goto_trace.steps.end();
          s_it2=goto_trace.steps.erase(s_it2));
        
      break;
    }

  #if 0
  show_goto_trace(std::cout, bmc.ns, test.goto_trace);
  #endif
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
  

  // should we minimise testsuite?
  if(!bmc.options.get_bool_option("disable-testsuite-minimisation"))
  {
    minimise_testsuite(tests, goal_map.size());
  }

  // report
  unsigned goals_covered=0;
  
  for(const auto & it : goal_map)
    if(it.second.satisfied) goals_covered++;

  switch(bmc.ui)
  {
    case ui_message_handlert::PLAIN:
    {
      status() << "\n** coverage results:" << eom;

      for(const auto & it : goal_map)
      {
        const goalt &goal=it.second;

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

        xmlt xml_result("goal");
        xml_result.set_attribute("id", id2string(it.first));
        xml_result.set_attribute("description", goal.description);
        xml_result.set_attribute("status", goal.satisfied?"SATISFIED":"FAILED");

        if(goal.source_location.is_not_nil())
          xml_result.new_element()=xml(goal.source_location);

        std::cout << xml_result << "\n";
      }

      for(const auto & test : tests)
      {
        xmlt xml_result("test");
        if(bmc.options.get_bool_option("trace"))
        {
          convert(bmc.ns, test.goto_trace, xml_result.new_element());
        }
        else
        {
          xmlt &xml_test=xml_result.new_element("inputs");

          for(const auto & step : test.goto_trace.steps)
          {
            if(step.is_input())
            {
              xmlt &xml_input=xml_test.new_element("input");
              xml_input.set_attribute("id", id2string(step.io_id));
              if(step.io_args.size()==1)
                xml_input.new_element("value")=
                  xml(step.io_args.front(), bmc.ns);
            }
          }
        }

        for(const auto & goal_id : test.covered_goals)
        {
          xmlt &xml_goal=xml_result.new_element("goal");
          xml_goal.set_attribute("id", id2string(goal_id));
        }
    
        std::cout << xml_result << "\n";
      }
      break;
    }

    case ui_message_handlert::JSON_UI:
    {
      json_objectt json_result;
      json_arrayt &goals_array=json_result["goals"].make_array();
      for(const auto & it : goal_map)
      {
        const goalt &goal=it.second;

        json_objectt &result=goals_array.push_back().make_object();
        result["status"]=json_stringt(goal.satisfied?"satisfied":"failed");
        result["goal"]=json_stringt(id2string(it.first));
        result["description"]=json_stringt(goal.description);

        if(goal.source_location.is_not_nil())
          result["sourceLocation"]=json(goal.source_location);
      }
      json_result["totalGoals"]=json_numbert(i2string(goal_map.size()));
      json_result["goalsCovered"]=json_numbert(i2string(goals_covered));

      json_arrayt &tests_array=json_result["tests"].make_array();
      for(const auto & test : tests)
      {
        json_objectt &result=tests_array.push_back().make_object();
        if(bmc.options.get_bool_option("trace"))
        {
          jsont &json_trace=result["trace"];
          convert(bmc.ns, test.goto_trace, json_trace);
        }
        else
        {
          json_arrayt &json_test=result["inputs"].make_array();

          for(const auto & step : test.goto_trace.steps)
          {
            if(step.is_input())
            {
              json_objectt json_input;
              json_input["id"]=json_stringt(id2string(step.io_id));
              if(step.io_args.size()==1)
                json_input["value"]=json(step.io_args.front(), bmc.ns);
              json_test.push_back(json_input);
            }
          }
        }
        json_arrayt &goal_refs=result["coveredGoals"].make_array();
        for(const auto & goal_id : test.covered_goals)
        {
          goal_refs.push_back(json_stringt(id2string(goal_id)));
        }
      }
      std::cout << ",\n" << json_result;
      break;
    }
  }

  status() << "** " << goals_covered
           << " of " << goal_map.size() << " covered ("
           << std::fixed << std::setw(1) << std::setprecision(1)
           << (goal_map.empty()?100.0:100.0*goals_covered/goal_map.size())
           << "%)" << eom;
           
  statistics() << "** Used "
               << cover_goals.iterations() << " iteration"
               << (cover_goals.iterations()==1?"":"s")
               << eom;

  if(bmc.ui==ui_message_handlert::PLAIN)
  {
    std::cout << "Test suite:" << '\n';

    for(const auto & test : tests)
      std::cout << get_test(test.goto_trace) << '\n';
  }
  
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
