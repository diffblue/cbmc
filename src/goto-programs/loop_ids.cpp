/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop IDs

#include "loop_ids.h"

#include <iostream>

#include <util/json_irep.h>
#include <util/xml_irep.h>

void show_loop_ids(
  ui_message_handlert::uit ui,
  const goto_modelt &goto_model)
{
  show_loop_ids(ui, goto_model.goto_functions);
}

void show_loop_ids(
  ui_message_handlert::uit ui,
  const irep_idt &function_id,
  const goto_programt &goto_program)
{
  switch(ui)
  {
    case ui_message_handlert::uit::PLAIN:
    {
      forall_goto_program_instructions(it, goto_program)
      {
        if(it->is_backwards_goto())
        {
          std::cout << "Loop " << goto_programt::loop_id(function_id, *it)
                    << ":"
                    << "\n";

          std::cout << "  " << it->source_location << "\n";
          std::cout << "\n";
        }
      }
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      forall_goto_program_instructions(it, goto_program)
      {
        if(it->is_backwards_goto())
        {
          std::string id = id2string(goto_programt::loop_id(function_id, *it));

          xmlt xml_loop("loop", {{"name", id}}, {});
          xml_loop.new_element("loop-id").data=id;
          xml_loop.new_element()=xml(it->source_location);
          std::cout << xml_loop << "\n";
        }
      }
      break;
    }
    case ui_message_handlert::uit::JSON_UI:
      UNREACHABLE; // use function below
  }
}

void show_loop_ids_json(
  ui_message_handlert::uit ui,
  const irep_idt &function_id,
  const goto_programt &goto_program,
  json_arrayt &loops)
{
  PRECONDITION(ui == ui_message_handlert::uit::JSON_UI); // use function above

  forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_backwards_goto())
    {
      std::string id = id2string(goto_programt::loop_id(function_id, *it));

      json_stringt name_json(id);
      jsont source_location_json(json(it->source_location));
      loops.push_back(
        json_objectt({{"name", std::move(name_json)},
                      {"sourceLocation", std::move(source_location_json)}}));
    }
  }
}

void show_loop_ids(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  switch(ui)
  {
    case ui_message_handlert::uit::PLAIN:
    case ui_message_handlert::uit::XML_UI:
      for(const auto &f: goto_functions.function_map)
        show_loop_ids(ui, f.first, f.second.body);
      break;

    case ui_message_handlert::uit::JSON_UI:
      json_objectt json_result;
      json_arrayt &loops=json_result["loops"].make_array();

      for(const auto &f : goto_functions.function_map)
        show_loop_ids_json(ui, f.first, f.second.body, loops);

      std::cout << ",\n" << json_result;
      break;
  }
}
