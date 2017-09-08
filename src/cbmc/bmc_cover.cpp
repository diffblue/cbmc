/*******************************************************************\

Module: Test-Suite Generation with BMC

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Test-Suite Generation with BMC

#include "bmc.h"

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

#include "bv_cbmc.h"

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

    // if satisfied, we compute a goto_trace
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

      for(const auto &goal_inst : instances)
        tmp.push_back(literal_exprt(goal_inst.condition));

      return disjunction(tmp);
    }
  };

  struct testt
  {
    goto_tracet goto_trace;
    std::vector<irep_idt> covered_goals;
  };

  inline irep_idt id(goto_programt::const_targett loc)
  {
    return loc->source_location.get_property_id();
  }

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;
  typedef std::vector<testt> testst;
  testst tests;

  std::string get_test(const goto_tracet &goto_trace) const
  {
    bool first=true;
    std::string test;
    for(const auto &step : goto_trace.steps)
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

void bmc_covert::satisfying_assignment()
{
  tests.push_back(testt());
  testt &test = tests.back();

  for(auto &goal_pair : goal_map)
  {
    goalt &g=goal_pair.second;

    // covered already?
    if(g.satisfied)
      continue;

    // check whether satisfied
    for(const auto &goal_inst : g.instances)
    {
      literalt cond=goal_inst.condition;

      if(solver.l_get(cond).is_true())
      {
        status() << "Covered function " << g.source_location.get_function()
                 << " " << g.description << messaget::eom;
        g.satisfied=true;
        test.covered_goals.push_back(goal_pair.first);
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
      goto_trace.steps.erase(++s_it1, goto_trace.steps.end());
      break;
    }

  #if 0
  show_goto_trace(std::cout, bmc.ns, test.goto_trace);
  #endif
}

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
    // Functions are already inlined.
    if(f_it->second.is_inlined()) continue;
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert())
        goal_map[id(i_it)]=
          goalt(
            id2string(i_it->source_location.get_comment()),
            i_it->source_location);
    }
  }

  for(auto &step : bmc.equation.SSA_steps)
    step.cond_literal=literalt(0, 0);

  // Do conversion to next solver layer

  bmc.do_conversion();

  // bmc.equation.output(std::cout);

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
        conjunction({ // NOLINT(whitespace/braces)
          literal_exprt(it->guard_literal),
          literal_exprt(!it->cond_literal) });
      literalt l_c=solver.convert(c);
      goal_map[id(it->source.pc)].add_instance(it, l_c);
    }
  }

  status() << "Aiming to cover " << goal_map.size() << " goal(s)" << eom;

  cover_goalst cover_goals(solver);

  cover_goals.register_observer(*this);

  for(const auto &g : goal_map)
  {
    literalt l=solver.convert(g.second.as_expr());
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

  for(const auto &g : goal_map)
    if(g.second.satisfied)
      goals_covered++;

  switch(bmc.ui)
  {
    case ui_message_handlert::uit::PLAIN:
    {
      status() << "\n** coverage results:" << eom;

      for(const auto &g : goal_map)
      {
        const goalt &goal=g.second;

        status() << "[" << g.first << "]";

        if(goal.source_location.is_not_nil())
          status() << ' ' << goal.source_location;

        if(!goal.description.empty())
          status() << ' ' << goal.description;

        status() << ": " << (goal.satisfied?"SATISFIED":"FAILED")
                 << eom;
      }

      status() << '\n';

      break;
    }

    case ui_message_handlert::uit::XML_UI:
    {
      for(const auto &goal_pair : goal_map)
      {
        const goalt &goal=goal_pair.second;

        xmlt xml_result("goal");
        xml_result.set_attribute("id", id2string(goal_pair.first));
        xml_result.set_attribute("description", goal.description);
        xml_result.set_attribute("status", goal.satisfied?"SATISFIED":"FAILED");

        if(goal.source_location.is_not_nil())
          xml_result.new_element()=xml(goal.source_location);

        std::cout << xml_result << "\n";
      }

      for(const auto &test : tests)
      {
        xmlt xml_result("test");
        if(bmc.options.get_bool_option("trace"))
        {
          convert(bmc.ns, test.goto_trace, xml_result.new_element());
        }
        else
        {
          xmlt &xml_test=xml_result.new_element("inputs");

          for(const auto &step : test.goto_trace.steps)
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

        for(const auto &goal_id : test.covered_goals)
        {
          xmlt &xml_goal=xml_result.new_element("goal");
          xml_goal.set_attribute("id", id2string(goal_id));
        }

        std::cout << xml_result << "\n";
      }
      break;
    }

    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_arrayt &goals_array=json_result["goals"].make_array();
      for(const auto &goal_pair : goal_map)
      {
        const goalt &goal=goal_pair.second;

        json_objectt &result=goals_array.push_back().make_object();
        result["status"]=json_stringt(goal.satisfied?"satisfied":"failed");
        result["goal"]=json_stringt(id2string(goal_pair.first));
        result["description"]=json_stringt(goal.description);

        if(goal.source_location.is_not_nil())
          result["sourceLocation"]=json(goal.source_location);
      }
      json_result["totalGoals"]=json_numbert(std::to_string(goal_map.size()));
      json_result["goalsCovered"]=json_numbert(std::to_string(goals_covered));

      json_arrayt &tests_array=json_result["tests"].make_array();
      for(const auto &test : tests)
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

          for(const auto &step : test.goto_trace.steps)
          {
            if(step.is_input())
            {
              json_objectt json_input;
              json_input["id"]=json_stringt(id2string(step.io_id));
              if(step.io_args.size()==1)
                json_input["value"]=
                  json(step.io_args.front(), bmc.ns, ID_unknown);
              json_test.push_back(json_input);
            }
          }
        }
        json_arrayt &goal_refs=result["coveredGoals"].make_array();
        for(const auto &goal_id : test.covered_goals)
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

  if(bmc.ui==ui_message_handlert::uit::PLAIN)
  {
    std::cout << "Test suite:" << '\n';

    for(const auto &test : tests)
      std::cout << get_test(test.goto_trace) << '\n';
  }

  return false;
}

/// Try to cover all goals
bool bmct::cover(
  const goto_functionst &goto_functions,
  const optionst::value_listt &criteria)
{
  bmc_covert bmc_cover(goto_functions, *this);
  bmc_cover.set_message_handler(get_message_handler());
  return bmc_cover();
}
