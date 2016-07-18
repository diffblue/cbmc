/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "show_analysis.h"

/*******************************************************************\

Function: show_analysist::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_analysist::show(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_functions, xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    output(ns, goto_functions, std::cout);
    break;
      
  default:;
  }
}

/*******************************************************************\

Function: show_analysist::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_analysist::show(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_programt &goto_program)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_program, xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    output(ns, goto_program, std::cout);
    break;
      
  default:;
  }
}
