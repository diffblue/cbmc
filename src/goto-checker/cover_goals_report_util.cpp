/*******************************************************************\

Module: Cover Goals Reporting Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Cover Goals Reporting Utilities

#include "cover_goals_report_util.h"

#include <iomanip>

#include <util/json.h>
#include <util/json_irep.h>
#include <util/json_stream.h>
#include <util/ui_message.h>
#include <util/xml.h>
#include <util/xml_irep.h>

static void output_goals_iterations(
  const propertiest &properties,
  unsigned iterations,
  messaget &log)
{
  const std::size_t goals_covered =
    count_properties(properties, property_statust::FAIL);
  log.status() << "** " << goals_covered << " of " << properties.size()
               << " covered (" << std::fixed << std::setw(1)
               << std::setprecision(1)
               << (properties.empty()
                     ? 100.0
                     : 100.0 * goals_covered / properties.size())
               << "%)" << messaget::eom;
  log.statistics() << "** Used " << iterations << " iteration"
                   << (iterations == 1 ? "" : "s") << messaget::eom;
}

static void output_goals_plain(const propertiest &properties, messaget &log)
{
  log.result() << "\n** coverage results:" << messaget::eom;

  for(const auto &property_pair : properties)
  {
    log.result() << "[" << property_pair.first << "]";

    if(property_pair.second.pc->source_location().is_not_nil())
      log.result() << ' ' << property_pair.second.pc->source_location();

    if(!property_pair.second.description.empty())
      log.result() << ' ' << property_pair.second.description;

    log.result() << ": "
                 << (property_pair.second.status == property_statust::FAIL
                       ? "SATISFIED"
                       : "FAILED")
                 << '\n';
  }

  log.result() << messaget::eom;
}

static void output_goals_xml(const propertiest &properties, messaget &log)
{
  for(const auto &property_pair : properties)
  {
    xmlt xml_result(
      "goal",
      {{"id", id2string(property_pair.first)},
       {"description", property_pair.second.description},
       {"status",
        property_pair.second.status == property_statust::FAIL ? "SATISFIED"
                                                              : "FAILED"}},
      {});

    const auto &source_location = property_pair.second.pc->source_location();
    if(source_location.is_not_nil())
    {
      xml_result.new_element() = xml(source_location);

      const irept &basic_block_lines =
        source_location.get_basic_block_source_lines();
      if(basic_block_lines.is_not_nil())
      {
        xmlt basic_block_lines_xml{"basic_block_lines"};
        for(const auto &file_entry : basic_block_lines.get_named_sub())
        {
          for(const auto &lines_entry : file_entry.second.get_named_sub())
          {
            xmlt line{"line"};
            line.set_attribute("file", id2string(file_entry.first));
            line.set_attribute("function", id2string(lines_entry.first));
            line.data = id2string(lines_entry.second.id());
            basic_block_lines_xml.new_element(line);
          }
        }
        xml_result.new_element(basic_block_lines_xml);
      }
    }

    log.result() << xml_result;
  }
}

static void output_goals_json(
  const propertiest &properties,
  messaget &log,
  ui_message_handlert &ui_message_handler)
{
  if(log.status().tellp() > 0)
    log.status() << messaget::eom; // force end of previous message
  json_stream_objectt &json_result =
    ui_message_handler.get_json_stream().push_back_stream_object();
  json_stream_arrayt &goals_array = json_result.push_back_stream_array("goals");
  for(const auto &property_pair : properties)
  {
    const property_infot &property_info = property_pair.second;

    json_objectt json_goal;
    json_goal["status"] = json_stringt(
      property_info.status == property_statust::FAIL ? "satisfied" : "failed");
    json_goal["goal"] = json_stringt(property_pair.first);
    json_goal["description"] = json_stringt(property_info.description);

    const auto &source_location = property_info.pc->source_location();
    if(source_location.is_not_nil())
    {
      json_goal["sourceLocation"] = json(source_location);

      const irept &basic_block_lines =
        source_location.get_basic_block_source_lines();
      if(basic_block_lines.is_not_nil())
      {
        json_objectt basic_block_lines_json;
        for(const auto &file_entry : basic_block_lines.get_named_sub())
        {
          json_objectt file_lines_json;
          for(const auto &lines_entry : file_entry.second.get_named_sub())
          {
            file_lines_json[id2string(lines_entry.first)] =
              json_stringt{lines_entry.second.id()};
          }
          basic_block_lines_json[id2string(file_entry.first)] = file_lines_json;
        }
        json_goal["basicBlockLines"] = basic_block_lines_json;
      }
    }

    goals_array.push_back(std::move(json_goal));
  }
  const std::size_t goals_covered =
    count_properties(properties, property_statust::FAIL);
  json_result.push_back(
    "goalsCovered", json_numbert(std::to_string(goals_covered)));
  json_result.push_back(
    "totalGoals", json_numbert(std::to_string(properties.size())));
}

void output_goals(
  const propertiest &properties,
  unsigned iterations,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
  {
    output_goals_plain(properties, log);
    break;
  }
  case ui_message_handlert::uit::XML_UI:
  {
    output_goals_xml(properties, log);
    break;
  }
  case ui_message_handlert::uit::JSON_UI:
  {
    output_goals_json(properties, log, ui_message_handler);
    break;
  }
  }
  output_goals_iterations(properties, iterations, log);
}
