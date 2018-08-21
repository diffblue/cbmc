/*******************************************************************\

Module: A GOTO Function

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Goto Function

#include "goto_function.h"

/// Return in \p dest the identifiers of the local variables declared in the \p
/// goto_function and the identifiers of the paramters of the \p goto_function.
void get_local_identifiers(
  const goto_functiont &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);

  const code_typet::parameterst &parameters = goto_function.type.parameters();

  // add parameters
  for(const auto &param : parameters)
  {
    const irep_idt &identifier = param.get_identifier();
    if(identifier != "")
      dest.insert(identifier);
  }
}
