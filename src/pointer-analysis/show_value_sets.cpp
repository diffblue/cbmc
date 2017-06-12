/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#include <iostream>

#include <util/xml.h>

#include "value_set_analysis.h"
#include "show_value_sets.h"

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(goto_functions, value_set_analysis, xml);
      std::cout << xml << std::endl;
    }
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(goto_functions, std::cout);
    break;

  default:
    {
    }
  }
}

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(goto_program, value_set_analysis, xml);
      std::cout << xml << std::endl;
    }
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(goto_program, std::cout);
    break;

  default:
    {
    }
  }
}
