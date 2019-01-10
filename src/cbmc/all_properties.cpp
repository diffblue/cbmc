/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "all_properties_class.h"

#include <algorithm>
#include <chrono>

#include <goto-checker/bmc_util.h>

#include <util/xml.h>
#include <util/json.h>

#include <solvers/sat/satcheck.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>

void bmc_all_propertiest::goal_covered(const cover_goalst::goalt &)
{
  for(auto &g : goal_map)
  {
    // failed already?
    if(g.second.status==goalt::statust::FAILURE)
      continue;

    // check whether failed
    for(auto &c : g.second.instances)
    {
      literalt cond=c->cond_literal;

      if(solver.l_get(cond).is_false())
      {
        g.second.status=goalt::statust::FAILURE;
        build_goto_trace(bmc.equation, c, solver, bmc.ns, g.second.goto_trace);
        break;
      }
    }
  }
}

safety_checkert::resultt bmc_all_propertiest::operator()()
{
  status() << "Passing problem to " << solver.decision_procedure_text() << eom;

  solver.set_message_handler(get_message_handler());

  auto solver_start=std::chrono::steady_clock::now();

  convert_symex_target_equation(
    bmc.equation, bmc.prop_conv, get_message_handler());
  bmc.freeze_program_variables();

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
          std::to_string(it->source.pc->loop_number);
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

  for(const auto &g : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    literalt p=!solver.convert(g.second.as_expr());
    cover_goals.add(p);
  }

  status() << "Running " << solver.decision_procedure_text() << eom;

  bool error=false;

  decision_proceduret::resultt result=cover_goals();

  if(result==decision_proceduret::resultt::D_ERROR)
  {
    error=true;
    for(auto &g : goal_map)
      if(g.second.status==goalt::statust::UNKNOWN)
        g.second.status=goalt::statust::ERROR;
  }
  else
  {
    for(auto &g : goal_map)
      if(g.second.status==goalt::statust::UNKNOWN)
        g.second.status=goalt::statust::SUCCESS;
  }

  {
    auto solver_stop = std::chrono::steady_clock::now();

    statistics()
      << "Runtime decision procedure: "
      << std::chrono::duration<double>(solver_stop - solver_start).count()
      << "s" << eom;
  }

  // report
  report(cover_goals);

  if(error)
    return safety_checkert::resultt::ERROR;

  bool safe=(cover_goals.number_covered()==0);

  if(safe)
    report_success(bmc.ui_message_handler); // legacy, might go away
  else
    report_failure(bmc.ui_message_handler); // legacy, might go away

  return safe?safety_checkert::resultt::SAFE:safety_checkert::resultt::UNSAFE;
}

void bmc_all_propertiest::report(const cover_goalst &cover_goals)
{
  switch(bmc.ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    {
      result() << "\n** Results:" << eom;

      // collect goals in a vector
      std::vector<goal_mapt::const_iterator> goals;

      for(auto g_it = goal_map.begin(); g_it != goal_map.end(); g_it++)
        goals.push_back(g_it);

      // now determine an ordering for those goals:
      // 1. alphabetical ordering of file name
      // 2. numerical ordering of line number
      // 3. alphabetical ordering of goal ID
      std::sort(
        goals.begin(),
        goals.end(),
        [](goal_mapt::const_iterator git1, goal_mapt::const_iterator git2) {
          const auto &g1 = git1->second.source_location;
          const auto &g2 = git2->second.source_location;
          if(g1.get_file() != g2.get_file())
            return id2string(g1.get_file()) < id2string(g2.get_file());
          else if(!g1.get_line().empty() && !g2.get_line().empty())
            return std::stoul(id2string(g1.get_line())) <
                   std::stoul(id2string(g2.get_line()));
          else
            return id2string(git1->first) < id2string(git2->first);
        });

      // now show in the order we have determined

      irep_idt previous_function;
      irep_idt current_file;
      for(const auto &g : goals)
      {
        const auto &l = g->second.source_location;

        if(l.get_function() != previous_function)
        {
          if(!previous_function.empty())
            result() << '\n';
          previous_function = l.get_function();
          if(!previous_function.empty())
          {
            current_file = l.get_file();
            if(!current_file.empty())
              result() << current_file << ' ';
            if(!l.get_function().empty())
              result() << "function " << l.get_function();
            result() << eom;
          }
        }

        result() << faint << '[' << g->first << "] " << reset;

        if(l.get_file() != current_file)
          result() << "file " << l.get_file() << ' ';

        if(!l.get_line().empty())
          result() << "line " << l.get_line() << ' ';

        result() << g->second.description << ": ";

        if(g->second.status == goalt::statust::SUCCESS)
          result() << green;
        else
          result() << red;

        result() << g->second.status_string() << reset << eom;
      }

      if(bmc.options.get_bool_option("trace"))
      {
        for(const auto &g : goal_map)
          if(g.second.status==goalt::statust::FAILURE)
          {
            result() << "\n" << "Trace for " << g.first << ":" << "\n";
            show_goto_trace(
              result(), bmc.ns, g.second.goto_trace, bmc.trace_options());
            result() << eom;
          }
      }

      status() << "\n** " << cover_goals.number_covered()
               << " of " << cover_goals.size() << " failed ("
               << cover_goals.iterations() << " iteration"
               << (cover_goals.iterations()==1?"":"s")
               << ")" << eom;
    }
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      for(const auto &g : goal_map)
      {
        xmlt xml_result(
          "result",
          {{"property", id2string(g.first)},
           {"status", g.second.status_string()}},
          {});

        if(g.second.status==goalt::statust::FAILURE)
          convert(bmc.ns, g.second.goto_trace, xml_result.new_element());

        result() << xml_result;
      }
      break;
    }

    case ui_message_handlert::uit::JSON_UI:
    {
      if(result().tellp() > 0)
        result() << eom; // force end of previous message
      json_stream_objectt &json_result =
        bmc.ui_message_handler.get_json_stream().push_back_stream_object();
      json_stream_arrayt &result_array =
        json_result.push_back_stream_array("result");

      for(const auto &g : goal_map)
      {
        json_stream_objectt &result = result_array.push_back_stream_object();
        result["property"] = json_stringt(g.first);
        result["description"] = json_stringt(g.second.description);
        result["status"]=json_stringt(g.second.status_string());

        if(g.second.status==goalt::statust::FAILURE)
        {
          json_stream_arrayt &json_trace =
            result.push_back_stream_array("trace");
          convert<json_stream_arrayt>(
            bmc.ns, g.second.goto_trace, json_trace, bmc.trace_options());
        }
      }
    }
    break;
  }
}

safety_checkert::resultt
bmct::all_properties(const goto_functionst &goto_functions)
{
  bmc_all_propertiest bmc_all_properties(goto_functions, prop_conv, *this);
  bmc_all_properties.set_message_handler(get_message_handler());
  return bmc_all_properties();
}
