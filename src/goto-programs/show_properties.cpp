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

void show_properties(
  const namespacet &ns,
  const irep_idt &identifier,
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
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

        std::cout << xml_property << '\n';
      }
      break;

    case ui_message_handlert::uit::JSON_UI:
      assert(false);
      break;

    case ui_message_handlert::uit::PLAIN:
      std::cout << "Property " << property_id << ":\n";

      std::cout << "  " << ins.source_location << '\n'
                << "  " << description << '\n'
                << "  " << from_expr(ns, identifier, ins.guard)
                        << '\n';

      std::cout << '\n';
      break;

    default:
      assert(false);
    }
  }
}


void show_properties_json(
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
    json_property["name"]=json_stringt(id2string(property_id));
    json_property["class"]=json_stringt(id2string(property_class));
    if(!source_location.get_basic_block_covered_lines().empty())
      json_property["coveredLines"]=
        json_stringt(
          id2string(source_location.get_basic_block_covered_lines()));
    json_property["sourceLocation"]=json(source_location);
    json_property["description"]=json_stringt(id2string(description));
    json_property["expression"]=
      json_stringt(from_expr(ns, identifier, ins.guard));
  }
}

void show_properties_json(
  const namespacet &ns,
  const goto_functionst &goto_functions)
{
  json_arrayt json_properties;

  for(const auto &fct : goto_functions.function_map)
    if(!fct.second.is_inlined())
      show_properties_json(
        json_properties,
        ns,
        fct.first,
        fct.second.body);

  json_objectt json_result;
  json_result["properties"] = json_properties;
  std::cout << ",\n" << json_result;
}

void show_properties(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, goto_functions);
  else
    for(const auto &fct : goto_functions.function_map)
      if(!fct.second.is_inlined())
        show_properties(ns, fct.first, ui, fct.second.body);
}

void show_properties(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  const namespacet ns(goto_model.symbol_table);
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, goto_model.goto_functions);
  else
    show_properties(ns, ui, goto_model.goto_functions);
}
