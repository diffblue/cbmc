/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ansi-c/cprover_library.h>

#include "link_to_library.h"
#include "compute_called_functions.h"
#include "goto_convert_functions.h"

/*******************************************************************\

Function: link_to_library

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void link_to_library(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  link_to_library(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
}

/*******************************************************************\

Function: link_to_library

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void link_to_library(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  // this needs a fixedpoint, as library functions
  // may depend on other library functions

  std::set<irep_idt> added_functions;

  while(true)
  {
    std::set<irep_idt> called_functions;
    compute_called_functions(goto_functions, called_functions);
  
    // eliminate those for which we already have a body

    std::set<irep_idt> missing_functions;

    for(std::set<irep_idt>::const_iterator
        it=called_functions.begin();
        it!=called_functions.end();
        it++)
    {
      goto_functionst::function_mapt::const_iterator
        f_it=goto_functions.function_map.find(*it);
      
      if(f_it!=goto_functions.function_map.end() &&
         f_it->second.body_available)
      {
        // it's overridden!
      }
      else if(added_functions.find(*it)!=added_functions.end())
      {
        // already added
      }
      else
        missing_functions.insert(*it);
    }
    
    // done?
    if(missing_functions.empty()) break;
    
    add_cprover_library(missing_functions, symbol_table, message_handler);

    // convert to CFG
    for(std::set<irep_idt>::const_iterator
        it=missing_functions.begin();
        it!=missing_functions.end();
        it++)
    {
      if(symbol_table.symbols.find(*it)!=symbol_table.symbols.end())
        goto_convert(*it, symbol_table, goto_functions, message_handler);
        
      added_functions.insert(*it);
    }
    
  }
}
