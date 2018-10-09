/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop IDs

#include "loop_ids.h"

#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/json.h>
#include <util/json_expr.h>

void show_loop_ids(
  ui_message_handlert::uit ui,
  const goto_modelt &goto_model)
{
  show_loop_ids(ui, goto_model.goto_functions);
}

void show_loop_ids(
  ui_message_handlert::uit ui,
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
          unsigned loop_id=it->loop_number;

          std::cout << "Loop "
                    << it->function << "." << loop_id << ":" << "\n";

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
          unsigned loop_id=it->loop_number;
          std::string id=id2string(it->function)+"."+std::to_string(loop_id);

          xmlt xml_loop("loop");
          xml_loop.set_attribute("name", id);
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
  const goto_programt &goto_program,
  json_arrayt &loops)
{
  assert(ui==ui_message_handlert::uit::JSON_UI); // use function above

  forall_goto_program_instructions(it, goto_program)
  {
    if(it->is_backwards_goto())
    {
      unsigned loop_id=it->loop_number;
      std::string id=id2string(it->function)+"."+std::to_string(loop_id);

      json_objectt &loop=loops.push_back().make_object();
      loop["name"]=json_stringt(id);
      loop["sourceLocation"]=json(it->source_location);
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
        show_loop_ids(ui, f.second.body);
      break;

    case ui_message_handlert::uit::JSON_UI:
      json_objectt json_result;
      json_arrayt &loops=json_result["loops"].make_array();

      for(const auto &f : goto_functions.function_map)
        show_loop_ids_json(ui, f.second.body, loops);

      std::cout << ",\n" << json_result;
      break;
  }
}
