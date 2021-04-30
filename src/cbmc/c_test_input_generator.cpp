/*******************************************************************\

Module: Test Input Generator for C

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Test Input Generator for C

#include "c_test_input_generator.h"

#include <goto-checker/goto_trace_storage.h>

#include <langapi/language_util.h>

#include <util/json.h>
#include <util/json_stream.h>
#include <util/options.h>
#include <util/string_utils.h>
#include <util/ui_message.h>
#include <util/xml.h>

#include <goto-programs/json_expr.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/xml_expr.h>
#include <goto-programs/xml_goto_trace.h>

c_test_input_generatort::c_test_input_generatort(
  ui_message_handlert &ui_message_handler,
  const optionst &options)
  : ui_message_handler(ui_message_handler), options(options)
{
}

void test_inputst::output_plain_text(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace) const
{
  const auto input_assignments =
    make_range(goto_trace.steps)
      .filter([](const goto_trace_stept &step) { return step.is_input(); })
      .map([ns](const goto_trace_stept &step) {
        return id2string(step.io_id) + '=' +
               from_expr(ns, step.function_id, step.io_args.front());
      });
  join_strings(out, input_assignments.begin(), input_assignments.end(), ", ");
  out << '\n';
}

json_objectt test_inputst::to_json(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  bool print_trace) const
{
  json_objectt json_result;
  json_arrayt &json_inputs = json_result["inputs"].make_array();

  for(const auto &step : goto_trace.steps)
  {
    if(step.is_input())
    {
      json_objectt json_input({{"id", json_stringt(step.io_id)}});
      if(step.io_args.size() == 1)
        json_input["value"] =
          json(step.io_args.front(), ns, ns.lookup(step.function_id).mode);
      json_inputs.push_back(std::move(json_input));
    }
  }

  json_arrayt goal_refs;
  for(const auto &goal_id : goto_trace.get_failed_property_ids())
  {
    goal_refs.push_back(json_stringt(goal_id));
  }
  json_result["coveredGoals"] = std::move(goal_refs);

  if(print_trace)
  {
    json_arrayt json_trace;
    convert(ns, goto_trace, json_trace);
    json_result["trace"] = std::move(json_trace);
  }
  return json_result;
}

xmlt test_inputst::to_xml(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  bool print_trace) const
{
  xmlt xml_result("test");
  if(print_trace)
  {
    convert(ns, goto_trace, xml_result.new_element());
  }
  else
  {
    xmlt &xml_test = xml_result.new_element("inputs");

    for(const auto &step : goto_trace.steps)
    {
      if(step.is_input())
      {
        xmlt &xml_input = xml_test.new_element("input");
        xml_input.set_attribute("id", id2string(step.io_id));
        if(step.io_args.size() == 1)
          xml_input.new_element("value") = xml(step.io_args.front(), ns);
      }
    }
  }

  for(const auto &goal_id : goto_trace.get_failed_property_ids())
  {
    xmlt &xml_goal = xml_result.new_element("goal");
    xml_goal.set_attribute("id", id2string(goal_id));
  }

  return xml_result;
}

test_inputst c_test_input_generatort::
operator()(const goto_tracet &goto_trace, const namespacet &ns)
{
  test_inputst test_inputs;
  return test_inputs;
}

void c_test_input_generatort::operator()(const goto_trace_storaget &traces)
{
  const namespacet &ns = traces.get_namespace();
  const bool print_trace = options.get_bool_option("trace");
  messaget log(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    log.result() << "\nTest suite:\n";
    for(const auto &trace : traces.all())
    {
      test_inputst test_inputs = (*this)(trace, ns);
      test_inputs.output_plain_text(log.result(), ns, trace);
    }
    log.result() << messaget::eom;
    break;
  case ui_message_handlert::uit::JSON_UI:
  {
    if(log.status().tellp() > 0)
      log.status() << messaget::eom; // force end of previous message
    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    json_stream_arrayt &tests_array =
      json_result.push_back_stream_array("tests");

    for(const auto &trace : traces.all())
    {
      test_inputst test_inputs = (*this)(trace, ns);
      tests_array.push_back(test_inputs.to_json(ns, trace, print_trace));
    }
    break;
  }
  case ui_message_handlert::uit::XML_UI:
    for(const auto &trace : traces.all())
    {
      test_inputst test_inputs = (*this)(trace, ns);
      log.result() << test_inputs.to_xml(ns, trace, print_trace);
    }
    break;
  }
}
