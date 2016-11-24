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
  
  const code_typet::parameterst &parameters=
    goto_function.type.parameters();
  
  // add parameters
  for(code_typet::parameterst::const_iterator
      a_it=parameters.begin();
      a_it!=parameters.end();
      a_it++)
  {
    const irep_idt &identifier=a_it->get_identifier();
    if(identifier!="") dest.insert(identifier);
  }
} 
