/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/xml.h>

#include "value_set_analysis.h"
#include "show_value_sets.h"

/*******************************************************************\

Function: show_value_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(goto_functions, value_set_analysis, xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    value_set_analysis.output(goto_functions, std::cout);
    break;
      
  default:;
  }
}

/*******************************************************************\

Function: show_value_sets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(goto_program, value_set_analysis, xml);
      std::cout << xml << std::endl;
    }
    break;
    
  case ui_message_handlert::PLAIN:
    value_set_analysis.output(goto_program, std::cout);
    break;
      
  default:;
  }
}
