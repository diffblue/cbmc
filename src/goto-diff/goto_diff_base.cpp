/*******************************************************************\

Module: GOTO-DIFF Base Class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// GOTO-DIFF Base Class

#include "goto_diff.h"

#include <util/json_irep.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/show_properties.h>

/// Output diff result
void goto_difft::output_functions() const
{
  messaget msg(message_handler);

  switch(message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
    {
      msg.result() << "total number of functions: " << total_functions_count
                   << '\n' << messaget::eom;
      output_function_group("new functions", new_functions, goto_model2);
      output_function_group(
        "modified functions", modified_functions, goto_model2);
      output_function_group(
        "deleted functions", deleted_functions, goto_model1);
      msg.result() << messaget::eom;
      break;
    }
    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result(
        {{"totalNumberOfFunctions",
          json_stringt(std::to_string(total_functions_count))}});
      convert_function_group_json(
        json_result["newFunctions"].make_array(), new_functions, goto_model2);
      convert_function_group_json(
        json_result["modifiedFunctions"].make_array(),
        modified_functions,
        goto_model2);
      convert_function_group_json(
        json_result["deletedFunctions"].make_array(),
        deleted_functions,
        goto_model1);
      msg.result() << json_result << messaget::eom;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      msg.error() << "XML output not supported yet" << messaget::eom;
    }
  }
}

/// Output group of functions in plain text format
/// \param group_name: the name of the group, e.g. "modified functions"
/// \param function_group: set of function ids in the group
/// \param goto_model: the goto model
void goto_difft::output_function_group(
  const std::string &group_name,
  const std::set<irep_idt> &function_group,
  const goto_modelt &goto_model) const
{
  messaget(message_handler).result() << group_name << ':' << messaget::eom;
  for(const auto &function_name : function_group)
  {
    output_function(function_name, goto_model);
  }
}

/// Output function information in plain text format
/// \param function_name: the function id
/// \param goto_model: the goto model
void goto_difft::output_function(
  const irep_idt &function_name,
  const goto_modelt &goto_model) const
{
  messaget msg(message_handler);

  namespacet ns(goto_model.symbol_table);
  const symbolt &symbol = ns.lookup(function_name);

  msg.result() << "  " << symbol.location.get_file() << ": " << function_name;

  if(options.get_bool_option("show-properties"))
  {
    const auto goto_function_it =
      goto_model.goto_functions.function_map.find(function_name);
    CHECK_RETURN(
      goto_function_it != goto_model.goto_functions.function_map.end());
    const goto_programt &goto_program = goto_function_it->second.body;

    for(const auto &ins : goto_program.instructions)
    {
      if(!ins.is_assert())
        continue;

      const source_locationt &source_location = ins.source_location;
      irep_idt property_id = source_location.get_property_id();
      msg.result() << "\n    " << property_id;
    }
  }

  msg.result() << messaget::eom;
}

/// Convert a function group to JSON
/// \param result: the JSON array to be populated
/// \param function_group: set of function ids in the group
/// \param goto_model: the goto model
void goto_difft::convert_function_group_json(
  json_arrayt &result,
  const std::set<irep_idt> &function_group,
  const goto_modelt &goto_model) const
{
  for(const auto &function_name : function_group)
  {
    convert_function_json(
      result.push_back(jsont()).make_object(), function_name, goto_model);
  }
}

/// Convert function information to JSON
/// \param result: the JSON object to be populated
/// \param function_name: the function id
/// \param goto_model: the goto model
void goto_difft::convert_function_json(
  json_objectt &result,
  const irep_idt &function_name,
  const goto_modelt &goto_model) const
{
  namespacet ns(goto_model.symbol_table);
  const symbolt &symbol = ns.lookup(function_name);

  result["name"] = json_stringt(function_name);
  result["sourceLocation"] = json(symbol.location);

  if(options.get_bool_option("show-properties"))
  {
    const auto goto_function_it =
      goto_model.goto_functions.function_map.find(function_name);
    CHECK_RETURN(
      goto_function_it != goto_model.goto_functions.function_map.end());
    const goto_programt &goto_program = goto_function_it->second.body;

    convert_properties_json(
      result["properties"].make_array(), ns, function_name, goto_program);
  }
}
