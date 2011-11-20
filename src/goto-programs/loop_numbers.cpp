/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <xml.h>
#include <xml_irep.h>
#include <i2string.h>

#include "loop_numbers.h"

/*******************************************************************\

Function: show_loop_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_loop_numbers(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
  for(goto_programt::instructionst::const_iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(it->is_backwards_goto())
    {
      unsigned loop_id=it->loop_number;

      if(ui==ui_message_handlert::XML_UI)
      {
        xmlt xml("loop");
        xml.new_element("loop-id").data=id2string(it->function)+"."+i2string(loop_id);
        
        xmlt &l=xml.new_element();
        convert(it->location, l);
        l.name="location";
        
        std::cout << xml << std::endl;
      }
      else if(ui==ui_message_handlert::PLAIN)
      {
        std::cout << "Loop "
                  << it->function << "." << loop_id << ":" << std::endl;

        std::cout << "  " << it->location << std::endl;
        std::cout << std::endl;
      }
      else
        assert(false);
    }
  }
}

/*******************************************************************\

Function: show_loop_numbers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_loop_numbers(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  for(goto_functionst::function_mapt::const_iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    show_loop_numbers(ui, it->second.body);
}
