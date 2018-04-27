/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show Value Sets

#include "show_value_sets.h"
#include "value_set_analysis.h"

#include <goto-programs/goto_model.h>

#include <util/namespace.h>
#include <util/xml.h>

#include <iostream>

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_modelt &goto_model,
  const value_set_analysist &value_set_analysis,
  const namespacet &ns)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(goto_model.goto_functions, value_set_analysis, xml);
      std::cout << xml << '\n';
    }
    break;

  case ui_message_handlert::uit::PLAIN:
    value_set_analysis.output(ns, goto_model.goto_functions, std::cout);
    break;

  default:
    {
    }
  }
}
