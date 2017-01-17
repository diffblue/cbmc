/*******************************************************************\

Module: Show goto functions

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/xml.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/xml_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>
#include <goto-programs/show_goto_functions_json.h>

#include "show_goto_functions.h"
#include "goto_functions.h"
#include "goto_model.h"

/*******************************************************************\

Function: cbmc_parseoptionst::show_goto_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions)
{
  switch(ui)
  {
  case ui_message_handlert::XML_UI:
  {
    //This only prints the list of functions
    xmlt xml_functions("functions");
    forall_goto_functions(it, goto_functions)
    {
      xmlt &xml_function=xml_functions.new_element("function");
      xml_function.set_attribute("name", id2string(it->first));
    }

    std::cout << xml_functions << std::endl;
  }
  break;

  case ui_message_handlert::JSON_UI:
  {
    show_goto_functions_jsont json_show_functions(ns);
    json_show_functions.show_goto_functions(goto_functions);
  }
  break;

  case ui_message_handlert::PLAIN:
    goto_functions.output(ns, std::cout);
    break;
  }
}

/*******************************************************************\

Function: show_goto_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_goto_functions(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_functions(ns, ui, goto_model.goto_functions);
}
