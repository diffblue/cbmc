/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Claims

#include "show_properties.h"

#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/json.h>
#include <util/json_expr.h>

#include <langapi/language_util.h>

#include "goto_functions.h"
#include "goto_model.h"


optionalt<source_locationt> find_property(
    const irep_idt &property,
    const goto_functionst & goto_functions)
{
  for(const auto &fct : goto_functions.function_map)
  {
    const goto_programt &goto_program = fct.second.body;

    for(const auto &ins : goto_program.instructions)
    {
      if(ins.is_assert())
      {
        if(ins.source_location.get_property_id() == property)
        {
          return ins.source_location;
        }
      }
    }
  }
  return { };
}

void show_properties(
  const namespacet &ns,
  const irep_idt &identifier,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
  messaget msg(message_handler);
  for(const auto &ins : goto_program.instructions)
  {
    if(!ins.is_assert())
      continue;

    const source_locationt &source_location=ins.source_location;

    const irep_idt &comment=source_location.get_comment();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description=
      (comment==""?"assertion":comment);

    irep_idt property_id=source_location.get_property_id();

    switch(ui)
    {
    case ui_message_handlert::uit::XML_UI:
      {
        // use me instead
        xmlt xml_property("property");
        xml_property.set_attribute("name", id2string(property_id));
        xml_property.set_attribute("class", id2string(property_class));

        xmlt &property_l=xml_property.new_element();
        property_l=xml(source_location);

        xml_property.new_element("description").data=id2string(description);
        xml_property.new_element("expression").data=
          from_expr(ns, identifier, ins.guard);

        msg.result() << xml_property;
      }
      break;

    case ui_message_handlert::uit::JSON_UI:
      UNREACHABLE;
      break;

    case ui_message_handlert::uit::PLAIN:
      msg.result() << "Property " << property_id << ":\n";

      msg.result() << "  " << ins.source_location << '\n'
                   << "  " << description << '\n'
                   << "  " << from_expr(ns, identifier, ins.guard) << '\n';

      msg.result() << messaget::eom;
      break;

    default:
      UNREACHABLE;
    }
  }
}

void convert_properties_json(
  json_arrayt &json_properties,
  const namespacet &ns,
  const irep_idt &identifier,
  const goto_programt &goto_program)
{
  for(const auto &ins : goto_program.instructions)
  {
    if(!ins.is_assert())
      continue;

    const source_locationt &source_location=ins.source_location;

    const irep_idt &comment=source_location.get_comment();
    // const irep_idt &function=location.get_function();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description=
      (comment==""?"assertion":comment);

    irep_idt property_id=source_location.get_property_id();

    json_objectt &json_property=
      json_properties.push_back(jsont()).make_object();
    json_property["name"] = json_stringt(property_id);
    json_property["class"] = json_stringt(property_class);
    if(!source_location.get_basic_block_covered_lines().empty())
      json_property["coveredLines"] =
        json_stringt(source_location.get_basic_block_covered_lines());
    json_property["sourceLocation"]=json(source_location);
    json_property["description"] = json_stringt(description);
    json_property["expression"]=
      json_stringt(from_expr(ns, identifier, ins.guard));
  }
}

void show_properties_json(
  const namespacet &ns,
  message_handlert &message_handler,
  const goto_functionst &goto_functions)
{
  messaget msg(message_handler);
  json_arrayt json_properties;

  for(const auto &fct : goto_functions.function_map)
    convert_properties_json(json_properties, ns, fct.first, fct.second.body);

  json_objectt json_result;
  json_result["properties"] = json_properties;
  msg.result() << json_result;
}

void show_properties(
  const namespacet &ns,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, message_handler, goto_functions);
  else
    for(const auto &fct : goto_functions.function_map)
      show_properties(ns, fct.first, message_handler, ui, fct.second.body);
}

void show_properties(
  const goto_modelt &goto_model,
  message_handlert &message_handler,
  ui_message_handlert::uit ui)
{
  const namespacet ns(goto_model.symbol_table);
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, message_handler, goto_model.goto_functions);
  else
    show_properties(ns, message_handler, ui, goto_model.goto_functions);
}
