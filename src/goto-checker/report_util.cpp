/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#include "report_util.h"

#include <algorithm>

#include <util/json.h>
#include <util/json_irep.h>
#include <util/ui_message.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include <goto-symex/build_goto_trace.h>

#include <goto-programs/json_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include "fault_localization_provider.h"
#include "goto_trace_storage.h"

#include "bmc_util.h"

void report_success(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION SUCCESSFUL" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data = "SUCCESS";
    msg.result() << xml;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_objectt json_result;
    json_result["cProverStatus"] = json_stringt("success");
    msg.result() << json_result;
  }
  break;
  }
}

void report_failure(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION FAILED" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data = "FAILURE";
    msg.result() << xml;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_objectt json_result;
    json_result["cProverStatus"] = json_stringt("failure");
    msg.result() << json_result;
  }
  break;
  }
}

void report_inconclusive(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION INCONCLUSIVE" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data = "INCONCLUSIVE";
    msg.result() << xml;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_objectt json_result;
    json_result["cProverStatus"] = json_stringt("inconclusive");
    msg.result() << json_result;
  }
  break;
  }
}

void report_error(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION ERROR" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data = "ERROR";
    msg.result() << xml;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_objectt json_result;
    json_result["cProverStatus"] = json_stringt("error");
    msg.result() << json_result;
  }
  break;
  }
}

static void output_single_assumption_plain(
  const assumption_infot &assumption_info,
  messaget &log,
  irep_idt current_file = irep_idt())
{
  const auto &l = assumption_info.pc->source_location;
  if(l.get_file() != current_file)
    log.result() << "file " << l.get_file() << ' ';
  if(!l.get_line().empty())
    log.result() << "line " << l.get_line() << ' ';
  log.result() << assumption_info.description << messaget::eom;
}

static void output_single_property_plain(
  const irep_idt &property_id,
  const property_infot &property_info,
  messaget &log,
  irep_idt current_file = irep_idt())
{
  const auto &l = property_info.pc->source_location;
  log.result() << messaget::faint << '[' << property_id << "] "
               << messaget::reset;
  if(l.get_file() != current_file)
    log.result() << "file " << l.get_file() << ' ';
  if(!l.get_line().empty())
    log.result() << "line " << l.get_line() << ' ';
  log.result() << property_info.description << ": ";
  switch(property_info.status)
  {
  case property_statust::NOT_CHECKED:
    log.result() << messaget::magenta;
    break;
  case property_statust::UNKNOWN:
    log.result() << messaget::yellow;
    break;
  case property_statust::NOT_REACHABLE:
    log.result() << messaget::bright_green;
    break;
  case property_statust::PASS:
    log.result() << messaget::green;
    break;
  case property_statust::FAIL:
    log.result() << messaget::red;
    break;
  case property_statust::ERROR:
    log.result() << messaget::bright_red;
    break;
  }
  log.result() << as_string(property_info.status) << messaget::reset
               << messaget::eom;
}

static std::vector<assumptionst::const_iterator>
get_sorted_assumptions(const assumptionst &assumptions)
{
  std::vector<assumptionst::const_iterator> sorted_assumptions;
  for(auto a_it = assumptions.begin(); a_it != assumptions.end(); a_it++)
    sorted_assumptions.push_back(a_it);
  // now determine an ordering for those goals:
  // 1. alphabetical ordering of file name
  // 2. numerical ordering of line number
  // 3. alphabetical ordering description
  std::sort(
    sorted_assumptions.begin(),
    sorted_assumptions.end(),
    [](assumptionst::const_iterator pit1, assumptionst::const_iterator pit2) {
      const auto &p1 = pit1->pc->source_location;
      const auto &p2 = pit2->pc->source_location;
      if(p1.get_file() != p2.get_file())
        return id2string(p1.get_file()) < id2string(p2.get_file());
      else if(!p1.get_line().empty() && !p2.get_line().empty())
      {
        return std::stoul(id2string(p1.get_line())) <
               std::stoul(id2string(p2.get_line()));
      }
      else
        return pit1->description < pit2->description;
    });
  return sorted_assumptions;
}

static std::vector<propertiest::const_iterator>
get_sorted_properties(const propertiest &properties)
{
  std::vector<propertiest::const_iterator> sorted_properties;
  for(auto p_it = properties.begin(); p_it != properties.end(); p_it++)
    sorted_properties.push_back(p_it);
  // now determine an ordering for those goals:
  // 1. alphabetical ordering of file name
  // 2. numerical ordering of line number
  // 3. alphabetical ordering of goal ID
  std::sort(
    sorted_properties.begin(),
    sorted_properties.end(),
    [](propertiest::const_iterator pit1, propertiest::const_iterator pit2) {
      const auto &p1 = pit1->second.pc->source_location;
      const auto &p2 = pit2->second.pc->source_location;
      if(p1.get_file() != p2.get_file())
        return id2string(p1.get_file()) < id2string(p2.get_file());
      else if(!p1.get_line().empty() && !p2.get_line().empty())
        return std::stoul(id2string(p1.get_line())) <
               std::stoul(id2string(p2.get_line()));
      else
        return id2string(pit1->first) < id2string(pit2->first);
    });
  return sorted_properties;
}

static void output_properties_plain(
  const std::vector<propertiest::const_iterator> &sorted_properties,
  const std::vector<assumptionst::const_iterator> &sorted_assumptions,
  messaget &log)
{
  if(sorted_properties.empty())
    return;

  // now show in the order we have determined
  irep_idt previous_function;
  irep_idt current_file;

  log.result() << "\n** Assumptions:" << messaget::eom;
  for(const auto &a : sorted_assumptions)
  {
    const auto &l = a->pc->source_location;
    if(l.get_function() != previous_function)
    {
      if(!previous_function.empty())
        log.result() << '\n';
      previous_function = l.get_function();
      if(!previous_function.empty())
      {
        current_file = l.get_file();
        if(!current_file.empty())
          log.result() << current_file << ' ';
        if(!l.get_function().empty())
          log.result() << "function " << l.get_function();
        log.result() << messaget::eom;
      }
    }
    output_single_assumption_plain(*a, log, current_file);
  }

  log.result() << "\n** Results:" << messaget::eom;
  for(const auto &p : sorted_properties)
  {
    const auto &l = p->second.pc->source_location;
    if(l.get_function() != previous_function)
    {
      if(!previous_function.empty())
        log.result() << '\n';
      previous_function = l.get_function();
      if(!previous_function.empty())
      {
        current_file = l.get_file();
        if(!current_file.empty())
          log.result() << current_file << ' ';
        if(!l.get_function().empty())
          log.result() << "function " << l.get_function();
        log.result() << messaget::eom;
      }
    }
    output_single_property_plain(p->first, p->second, log, current_file);
  }
}

static void output_iterations(
  const propertiest &properties,
  std::size_t iterations,
  messaget &log)
{
  if(properties.empty())
    return;

  log.status() << "\n** "
               << count_properties(properties, property_statust::FAIL) << " of "
               << properties.size() << " failed (" << iterations
               << " iterations)" << messaget::eom;
}

void output_properties(
  const assumptionst &assumptions,
  const propertiest &properties,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    const auto sorted_properties = get_sorted_properties(properties);
    const auto sorted_assumptions = get_sorted_assumptions(assumptions);
    output_properties_plain(sorted_properties, sorted_assumptions, log);
    output_iterations(properties, iterations, log);
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    for(const auto &assumption: assumptions)
      log.result() << xml(assumption);

    for(const auto &property_pair : properties)
    {
      log.result() << xml(property_pair.first, property_pair.second);
    }
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_assumptions =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &assumptions_array =
      json_assumptions.push_back_stream_array("assumptions");
    for(const auto &assumption : assumptions)
    {
      assumptions_array.push_back(
        json(assumption));
    }

    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &result_array =
      json_result.push_back_stream_array("result");
    for(const auto &property_pair : properties)
    {
      result_array.push_back(json(property_pair.first, property_pair.second));
    }
    break;
  }
  }
}

void output_properties_with_traces(
  const assumptionst &assumptions,
  const propertiest &properties,
  const goto_trace_storaget &traces,
  const trace_optionst &trace_options,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    const auto sorted_properties = get_sorted_properties(properties);
    const auto sorted_assumptions = get_sorted_assumptions(assumptions);
    output_properties_plain(sorted_properties, sorted_assumptions, log);
    for(const auto &property_it : sorted_properties)
    {
      if(property_it->second.status == property_statust::FAIL)
      {
        log.result() << "\n"
                     << "Trace for " << property_it->first << ":"
                     << "\n";
        show_goto_trace(
          log.result(),
          traces.get_namespace(),
          traces[property_it->first],
          trace_options);
        log.result() << messaget::eom;
      }
    }
    output_iterations(properties, iterations, log);
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    for(const auto &assumption: assumptions)
      log.result() << xml(assumption);

    for(const auto &property_pair : properties)
    {
      xmlt xml_result = xml(property_pair.first, property_pair.second);
      if(property_pair.second.status == property_statust::FAIL)
      {
        convert(
          traces.get_namespace(),
          traces[property_pair.first],
          xml_result.new_element());
      }
      log.result() << xml_result;
    }
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_assumptions =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &assumptions_array =
      json_assumptions.push_back_stream_array("assumptions");
    for(const auto &assumption : assumptions)
    {
      assumptions_array.push_back(
        json(assumption));
    }

    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &result_array =
      json_result.push_back_stream_array("result");
    for(const auto &property_pair : properties)
    {
      json_stream_objectt &json_property =
        result_array.push_back_stream_object();
      json(json_property, property_pair.first, property_pair.second);
      if(property_pair.second.status == property_statust::FAIL)
      {
        json_stream_arrayt &json_trace =
          json_property.push_back_stream_array("trace");
        convert<json_stream_arrayt>(
          traces.get_namespace(),
          traces[property_pair.first],
          json_trace,
          trace_options);
      }
    }
    break;
  }
  }
}

void output_fault_localization_scores(
  const fault_location_infot &fault_location,
  messaget &log)
{
  log.conditional_output(
    log.debug(), [fault_location](messaget::mstreamt &out) {
      out << "Fault localization scores:" << messaget::eom;
      for(auto &score_pair : fault_location.scores)
      {
        out << score_pair.first->source_location
            << "\n  score: " << score_pair.second << messaget::eom;
      }
    });
}

static goto_programt::const_targett
max_fault_localization_score(const fault_location_infot &fault_location)
{
  PRECONDITION(!fault_location.scores.empty());

  return std::max_element(
           fault_location.scores.begin(),
           fault_location.scores.end(),
           [](
             fault_location_infot::score_mapt::value_type score_pair1,
             fault_location_infot::score_mapt::value_type score_pair2) {
             return score_pair1.second < score_pair2.second;
           })
    ->first;
}

static void output_fault_localization_plain(
  const irep_idt &property_id,
  const fault_location_infot &fault_location,
  messaget &log)
{
  if(fault_location.scores.empty())
  {
    log.result() << "[" + id2string(property_id) + "]: \n"
                 << "   unable to localize fault" << messaget::eom;
    return;
  }

  output_fault_localization_scores(fault_location, log);
  log.result() << "[" + id2string(property_id) + "]: \n  "
               << max_fault_localization_score(fault_location)->source_location
               << messaget::eom;
}

static void output_fault_localization_plain(
  const std::unordered_map<irep_idt, fault_location_infot> &fault_locations,
  messaget &log)
{
  log.result() << "\n** Most likely fault location:" << messaget::eom;
  for(const auto fault_location_pair : fault_locations)
  {
    output_fault_localization_plain(
      fault_location_pair.first, fault_location_pair.second, log);
  }
}

static xmlt xml(
  const irep_idt &property_id,
  const fault_location_infot &fault_location,
  messaget &log)
{
  xmlt xml_diagnosis("diagnosis");

  xml_diagnosis.set_attribute("property", id2string(property_id));

  if(fault_location.scores.empty())
  {
    xml_diagnosis.new_element("result").data = "unable to localize fault";
    return xml_diagnosis;
  }

  output_fault_localization_scores(fault_location, log);

  xmlt xml_location =
    xml(max_fault_localization_score(fault_location)->source_location);
  xml_diagnosis.new_element("result").new_element().swap(xml_location);

  return xml_diagnosis;
}

static void output_fault_localization_xml(
  const std::unordered_map<irep_idt, fault_location_infot> &fault_locations,
  messaget &log)
{
  xmlt dest("fault-localization");
  for(const auto fault_location_pair : fault_locations)
  {
    xmlt xml_diagnosis =
      xml(fault_location_pair.first, fault_location_pair.second, log);
    dest.new_element().swap(xml_diagnosis);
  }
  log.result() << dest;
}

static json_objectt json(const fault_location_infot &fault_location)
{
  json_objectt json_result;
  if(fault_location.scores.empty())
  {
    json_result["result"] = json_stringt("unable to localize fault");
  }
  else
  {
    json_result["result"] =
      json(max_fault_localization_score(fault_location)->source_location);
  }
  return json_result;
}

void output_properties_with_fault_localization(
  const assumptionst &assumptions,
  const propertiest &properties,
  const std::unordered_map<irep_idt, fault_location_infot> &fault_locations,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    output_properties(assumptions, properties, iterations, ui_message_handler);
    output_fault_localization_plain(fault_locations, log);
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_assumptions =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &assumptions_array =
      json_assumptions.push_back_stream_array("assumptions");
    for(const auto &assumption : assumptions)
    {
      assumptions_array.push_back(
        json(assumption));
    }

    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &result_array =
      json_result.push_back_stream_array("result");
    for(const auto &property_pair : properties)
    {
      json_stream_objectt &json_property =
        result_array.push_back_stream_object();
      json(json_property, property_pair.first, property_pair.second);
      if(property_pair.second.status == property_statust::FAIL)
      {
        json_property.push_back(
          "diagnosis", json(fault_locations.at(property_pair.first)));
      }
    }
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    output_properties(assumptions, properties, iterations, ui_message_handler);
    output_fault_localization_xml(fault_locations, log);
    break;
  }
  }
}

void output_properties_with_traces_and_fault_localization(
  const assumptionst &assumptions,
  const propertiest &properties,
  const goto_trace_storaget &traces,
  const trace_optionst &trace_options,
  const std::unordered_map<irep_idt, fault_location_infot> &fault_locations,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    output_properties_with_traces(
      assumptions, properties, traces, trace_options, iterations, ui_message_handler);
    output_fault_localization_plain(fault_locations, log);
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_assumptions =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &assumptions_array =
      json_assumptions.push_back_stream_array("assumptions");
    for(const auto &assumption : assumptions)
    {
      assumptions_array.push_back(
        json(assumption));
    }

    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &result_array =
      json_result.push_back_stream_array("result");
    for(const auto &property_pair : properties)
    {
      json_stream_objectt &json_property =
        result_array.push_back_stream_object();
      json(json_property, property_pair.first, property_pair.second);
      if(property_pair.second.status == property_statust::FAIL)
      {
        json_stream_arrayt &json_trace =
          json_property.push_back_stream_array("trace");
        convert<json_stream_arrayt>(
          traces.get_namespace(),
          traces[property_pair.first],
          json_trace,
          trace_options);
        json_property.push_back(
          "diagnosis", json(fault_locations.at(property_pair.first)));
      }
    }
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    output_properties_with_traces(
      assumptions, properties, traces, trace_options, iterations, ui_message_handler);
    output_fault_localization_xml(fault_locations, log);
    break;
  }
  }
}

void output_error_trace_with_fault_localization(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const trace_optionst &trace_options,
  const fault_location_infot &fault_location_info,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    output_error_trace(goto_trace, ns, trace_options, ui_message_handler);
    output_fault_localization_plain(
      goto_trace.get_last_step().property_id, fault_location_info, log);
    break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    const goto_trace_stept &step = goto_trace.get_last_step();
    json_result["property"] = json_stringt(step.property_id);
    json_result["description"] = json_stringt(step.comment);
    json_result["status"] = json_stringt("failed");
    json_stream_arrayt &json_trace =
      json_result.push_back_stream_array("trace");
    convert<json_stream_arrayt>(ns, goto_trace, json_trace, trace_options);
    json_result.push_back("diagnosis", json(fault_location_info));
    break;
  }

  case ui_message_handlert::uit::XML_UI:
  {
    output_error_trace(goto_trace, ns, trace_options, ui_message_handler);
    xmlt dest(
      "fault-localization",
      {},
      {xml(goto_trace.get_last_step().property_id, fault_location_info, log)});
    log.result() << dest;
    break;
  }
  }
}

void output_overall_result(
  resultt result,
  ui_message_handlert &ui_message_handler)
{
  switch(result)
  {
  case resultt::PASS:
    report_success(ui_message_handler);
    break;
  case resultt::FAIL:
    report_failure(ui_message_handler);
    break;
  case resultt::UNKNOWN:
    report_inconclusive(ui_message_handler);
    break;
  case resultt::ERROR:
    report_error(ui_message_handler);
    break;
  }
}
