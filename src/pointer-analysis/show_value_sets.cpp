/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#include "show_value_sets.h"
#include "value_set_analysis.h"

#include <util/xml.h>

#include <iostream>

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_modelt &goto_model,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    std::cout << value_set_analysis.output_xml(goto_model);
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(goto_model, std::cout);
    break;

  case ui_message_handlert::uit::JSON_UI:
    std::cout << value_set_analysis.output_json(goto_model);
    break;
  }
}

void show_value_sets(
  ui_message_handlert::uit ui,
  const namespacet &ns,
  const irep_idt &function_name,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    std::cout << value_set_analysis.output_xml(ns, function_name, goto_program);
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(ns, function_name, goto_program, std::cout);
    break;

  case ui_message_handlert::uit::JSON_UI:
    std::cout << value_set_analysis.output_json(
      ns, function_name, goto_program);
    break;
  }
}
