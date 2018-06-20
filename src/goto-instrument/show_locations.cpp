/*******************************************************************\

Module: Show program locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show program locations

#include "show_locations.h"

#include <iostream>

#include <util/xml.h>
#include <util/xml_irep.h>

#include <langapi/language_util.h>

#include <goto-programs/goto_model.h>

void show_locations(
  ui_message_handlert::uit ui,
  const irep_idt function_id,
  const goto_programt &goto_program)
{
  for(goto_programt::instructionst::const_iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    const source_locationt &source_location=it->source_location;

    switch(ui)
    {
    case ui_message_handlert::uit::XML_UI:
      {
        xmlt xml("program_location");
        xml.new_element("function").data=id2string(function_id);
        xml.new_element("id").data=std::to_string(it->location_number);

        xmlt &l=xml.new_element();
        l.name="location";

        l.new_element("line").data=id2string(source_location.get_line());
        l.new_element("file").data=id2string(source_location.get_file());
        l.new_element("function").data=
          id2string(source_location.get_function());

        std::cout << xml << '\n';
      }
      break;

    case ui_message_handlert::uit::PLAIN:
      std::cout << function_id << " "
                << it->location_number << " "
                << it->source_location << '\n';
      break;

    case ui_message_handlert::uit::JSON_UI:
      UNREACHABLE;
    }
  }
}

void show_locations(
  ui_message_handlert::uit ui,
  const goto_modelt &goto_model)
{
  for(const auto &f : goto_model.goto_functions.function_map)
    show_locations(ui, f.first, f.second.body);
}
