/*******************************************************************\

Module: Show Claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Claims

#include "show_properties.h"

#include <util/json_irep.h>
#include <util/ui_message.h>
#include <util/xml_irep.h>

#include <langapi/language_util.h>

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
        if(ins.source_location().get_property_id() == property)
        {
          return ins.source_location();
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

    const source_locationt &source_location = ins.source_location();

    const irep_idt &comment=source_location.get_comment();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description = (comment.empty() ? "assertion" : comment);

    irep_idt property_id=source_location.get_property_id();

    switch(ui)
    {
    case ui_message_handlert::uit::XML_UI:
      {
        // use me instead
        xmlt xml_property(
          "property",
          {{"name", id2string(property_id)},
           {"class", id2string(property_class)}},
          {});

        xmlt &property_l=xml_property.new_element();
        property_l=xml(source_location);

        xml_property.new_element("description").data=id2string(description);
        xml_property.new_element("expression").data =
          from_expr(ns, identifier, ins.condition());

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
          xml_property.new_element(basic_block_lines_xml);
        }

        msg.result() << xml_property;
      }
      break;

    case ui_message_handlert::uit::JSON_UI:
      UNREACHABLE;
      break;

    case ui_message_handlert::uit::PLAIN:
      msg.result() << "Property " << property_id << ":\n";

      msg.result() << "  " << ins.source_location() << '\n'
                   << "  " << description << '\n'
                   << "  " << from_expr(ns, identifier, ins.condition())
                   << '\n';

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

    const source_locationt &source_location = ins.source_location();

    const irep_idt &comment=source_location.get_comment();
    // const irep_idt &function=location.get_function();
    const irep_idt &property_class=source_location.get_property_class();
    const irep_idt description = (comment.empty() ? "assertion" : comment);

    irep_idt property_id=source_location.get_property_id();

    json_objectt json_property{
      {"name", json_stringt(property_id)},
      {"class", json_stringt(property_class)},
      {"sourceLocation", json(source_location)},
      {"description", json_stringt(description)},
      {"expression", json_stringt(from_expr(ns, identifier, ins.condition()))}};

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
      json_property["basicBlockLines"] = basic_block_lines_json;
    }

    json_properties.push_back(std::move(json_property));
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

  json_objectt json_result{{"properties", json_properties}};
  msg.result() << json_result;
}

void show_properties(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions)
{
  ui_message_handlert::uit ui = ui_message_handler.get_ui();
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, ui_message_handler, goto_functions);
  else
    for(const auto &fct : goto_functions.function_map)
      show_properties(ns, fct.first, ui_message_handler, ui, fct.second.body);
}

void show_properties(
  const goto_modelt &goto_model,
  ui_message_handlert &ui_message_handler)
{
  ui_message_handlert::uit ui = ui_message_handler.get_ui();
  const namespacet ns(goto_model.symbol_table);
  if(ui == ui_message_handlert::uit::JSON_UI)
    show_properties_json(ns, ui_message_handler, goto_model.goto_functions);
  else
    show_properties(ns, ui_message_handler, goto_model.goto_functions);
}
