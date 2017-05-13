/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#include "goto_functions.h"

void get_local_identifiers(
  const goto_function_templatet<goto_programt> &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);

  const code_typet::parameterst &parameters=
    goto_function.type.parameters();

  // add parameters
  for(const auto &param : parameters)
  {
    const irep_idt &identifier=param.get_identifier();
    if(identifier!="")
      dest.insert(identifier);
  }
}

/// Ensure that all functions satisfy all assumptions about
/// consistent goto programs.
/// \param msg Message output
/// \return True, iff at least one invariant is violated
bool goto_functionst::check_internal_invariants(messaget &msg) const
{
  forall_goto_functions(it, *this)
    if(it->second.body.check_internal_invariants(msg))
      return true;

  return false;
}
