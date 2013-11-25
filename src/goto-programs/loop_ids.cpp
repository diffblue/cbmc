/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/i2string.h>

#include "loop_ids.h"

/*******************************************************************\

Function: show_loop_ids

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_loop_ids(
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
        xmlt xml_loop("loop");
        xml_loop.new_element("loop-id").data=id2string(it->function)+"."+i2string(loop_id);
        xml_loop.new_element()=xml(it->location);
        std::cout << xml_loop << std::endl;
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

Function: show_loop_ids

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_loop_ids(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    show_loop_ids(ui, it->second.body);
}
