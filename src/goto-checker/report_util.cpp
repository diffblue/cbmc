/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#include "report_util.h"

#include <algorithm>

#include <util/json.h>
#include <util/ui_message.h>
#include <util/xml.h>

#include <goto-symex/build_goto_trace.h>

#include <goto-programs/json_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include "goto_trace_storage.h"

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

static void
output_properties_plain(const propertiest &properties, messaget &log)
{
  if(properties.empty())
    return;

  log.result() << "\n** Results:" << messaget::eom;
  // collect properties in a vector
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
  // now show in the order we have determined
  irep_idt previous_function;
  irep_idt current_file;
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
  const propertiest &properties,
  std::size_t iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    output_properties_plain(properties, log);
    output_iterations(properties, iterations, log);
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    for(const auto &property_pair : properties)
    {
      log.result() << xml(property_pair.first, property_pair.second);
    }
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
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
    output_properties_plain(properties, log);
    for(const auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::FAIL)
      {
        log.result() << "\n"
                     << "Trace for " << property_pair.first << ":"
                     << "\n";
        show_goto_trace(
          log.result(),
          traces.get_namespace(),
          traces[property_pair.first],
          trace_options);
        log.result() << messaget::eom;
      }
    }
    output_iterations(properties, iterations, log);
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
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
