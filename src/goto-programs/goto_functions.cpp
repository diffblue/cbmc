/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#include "goto_functions.h"

/*******************************************************************\

Function: get_local_identifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_local_identifiers(
  const goto_function_templatet<goto_programt> &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);
  
  const code_typet::argumentst &arguments=
    goto_function.type.arguments();
  
  // add arguments
  for(code_typet::argumentst::const_iterator
      a_it=arguments.begin();
      a_it!=arguments.end();
      a_it++)
  {
    const irep_idt &identifier=a_it->get_identifier();
    if(identifier!="") dest.insert(identifier);
  }
} 
