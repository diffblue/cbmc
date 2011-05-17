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
  contextt &context,
  goto_functionst &goto_functions,
  const optionst &options,
  message_handlert &message_handler)
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
    else
      missing_functions.insert(*it);
  }
  
  add_cprover_library(missing_functions, context, message_handler);

  // convert to CFG
  for(std::set<irep_idt>::const_iterator
      it=missing_functions.begin();
      it!=missing_functions.end();
      it++)
  {
    if(context.symbols.find(*it)!=context.symbols.end())
      goto_convert(*it, context, options, goto_functions, message_handler);
  }
}
