/*******************************************************************\

Module: Symex Test Suite Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symex Test Suite Generation

#include "symex_parse_options.h"

#include <iostream>

#include <util/json_expr.h>
#include <util/xml_expr.h>

#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>

std::string symex_parse_optionst::get_test(const goto_tracet &goto_trace)
{
  bool first=true;
  std::string test;
  const namespacet ns(goto_model.symbol_table);

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
        test+=from_expr(ns, "", step.io_args.front());
    }
  }
  return test;
}

void symex_parse_optionst::report_cover(
  const path_searcht::property_mapt &property_map)
{
  // report
  unsigned goals_covered=0;

  for(const auto &prop_pair : property_map)
    if(prop_pair.second.is_failure())
      goals_covered++;

  switch(get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
    {
      status() << "\n** coverage results:" << eom;

      for(const auto &prop_pair : property_map)
      {
        const auto &property=prop_pair.second;

        status() << "[" << prop_pair.first << "]";

        if(property.source_location.is_not_nil())
          status() << ' ' << property.source_location;

        if(!property.description.empty())
          status() << ' ' << property.description;

        status() << ": " << (property.is_failure()?"SATISFIED":"FAILED")
                 << eom;
      }

      status() << '\n';

      break;
    }

    case ui_message_handlert::uit::XML_UI:
    {
      for(const auto &prop_pair : property_map)
      {
        const auto &property=prop_pair.second;

        xmlt xml_result("result");
        xml_result.set_attribute("goal", id2string(prop_pair.first));
        xml_result.set_attribute(
          "description", id2string(property.description));
        xml_result.set_attribute(
          "status", property.is_failure()?"SATISFIED":"FAILED");

        if(property.source_location.is_not_nil())
          xml_result.new_element()=xml(property.source_location);

        if(property.is_failure())
        {
          const namespacet ns(goto_model.symbol_table);

          if(cmdline.isset("trace"))
          {
            convert(ns, property.error_trace, xml_result.new_element());
          }
          else
          {
            xmlt &xml_test=xml_result.new_element("test");

            for(const auto &step : property.error_trace.steps)
            {
              if(step.is_input())
              {
                xmlt &xml_input=xml_test.new_element("input");
                xml_input.set_attribute("id", id2string(step.io_id));
                if(step.io_args.size()==1)
                  xml_input.new_element("value")=
                    xml(step.io_args.front(), ns);
              }
            }
          }
        }

        std::cout << xml_result << "\n";
      }

      break;
    }
    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_arrayt &result_array=json_result["results"].make_array();
      for(const auto &prop_pair : property_map)
      {
        const auto &property=prop_pair.second;

        json_objectt &result=result_array.push_back().make_object();
        result["status"]=
          json_stringt(property.is_failure()?"satisfied":"failed");
        result["goal"]=json_stringt(id2string(prop_pair.first));
        result["description"]=json_stringt(id2string(property.description));

        if(property.source_location.is_not_nil())
          result["sourceLocation"]=json(property.source_location);

        if(property.is_failure())
        {
          const namespacet ns(goto_model.symbol_table);

          if(cmdline.isset("trace"))
          {
            jsont &json_trace=result["trace"];
            convert(ns, property.error_trace, json_trace);
          }
          else
          {
            json_arrayt &json_test=result["test"].make_array();

            for(const auto &step : property.error_trace.steps)
            {
              if(step.is_input())
              {
                json_objectt json_input;
                json_input["id"]=json_stringt(id2string(step.io_id));
                if(step.io_args.size()==1)
                  json_input["value"]=json(step.io_args.front(), ns);
                json_test.push_back(json_input);
              }
            }
          }
        }
      }
      json_result["totalGoals"]=
        json_numbert(std::to_string(property_map.size()));
      json_result["goalsCovered"]=json_numbert(std::to_string(goals_covered));
      std::cout << ",\n" << json_result;
      break;
    }
  }

  status() << "** " << goals_covered
           << " of " << property_map.size() << " covered ("
           << std::fixed << std::setw(1) << std::setprecision(1)
           << (property_map.empty()?
               100.0:100.0*goals_covered/property_map.size())
           << "%)"
           << eom;

  if(get_ui()==ui_message_handlert::uit::PLAIN)
  {
    std::set<std::string> tests;

    for(const auto &prop_pair : property_map)
      if(prop_pair.second.is_failure())
        tests.insert(get_test(prop_pair.second.error_trace));

    std::cout << "Test suite:" << '\n';

    for(const auto &t : tests)
      std::cout << t << '\n';
  }
}
