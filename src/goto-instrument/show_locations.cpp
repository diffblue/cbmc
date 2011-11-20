/*******************************************************************\

Module: Show program locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <xml.h>
#include <i2string.h>
#include <xml_irep.h>

#include <langapi/language_util.h>

#include "show_locations.h"

/*******************************************************************\

Function: show_locations

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    const locationt &location=it->location;
      
    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml("program_location");
        xml.new_element("function").data=id2string(function_id);
        xml.new_element("id").data=i2string(it->location_number);
        
        xmlt &l=xml.new_element();
        l.name="location";
        
        l.new_element("line").data=id2string(location.get_line());
        l.new_element("file").data=id2string(location.get_file());
        l.new_element("function").data=id2string(location.get_function());
        
        std::cout << xml << std::endl;
      }
      break;
      
    case ui_message_handlert::PLAIN:
      std::cout << function_id << " "
                << it->location_number << " "
                << it->location << std::endl;
      break;

    default:
      assert(false);
    }
  }
}

/*******************************************************************\

Function: show_locations

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_locations(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    show_locations(ui, it->first, it->second.body);
}
