/*******************************************************************\

Module: Show goto functions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Show goto functions

#include "show_goto_functions.h"

#include <iostream>

#include <util/xml.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/xml_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>

#include <langapi/language_util.h>
#include <goto-programs/show_goto_functions_json.h>
#include <goto-programs/show_goto_functions_xml.h>

#include "goto_functions.h"
#include "goto_model.h"

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  bool list_only)
{
  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
  {
    show_goto_functions_xmlt xml_show_functions(ns, list_only);
    xml_show_functions(goto_functions, std::cout);
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    show_goto_functions_jsont json_show_functions(ns, list_only);
    json_show_functions(goto_functions, std::cout);
  }
  break;

  case ui_message_handlert::uit::PLAIN:
    if(list_only)
    {
      for(const auto &fun : goto_functions.function_map)
      {
        const symbolt &symbol = ns.lookup(fun.first);
        std::cout << '\n'
                  << symbol.display_name() << " /* " << symbol.name
                  << (fun.second.body_available() ? ""
                                                  : ", body not available")
                  << " */";
      }

      std::cout << std::endl;
    }
    else
      goto_functions.output(ns, std::cout);

    break;
  }
}

void show_goto_functions(
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui,
  bool list_only)
{
  const namespacet ns(goto_model.symbol_table);
  show_goto_functions(ns, ui, goto_model.goto_functions, list_only);
}
