/*******************************************************************\

Module: A GOTO Function

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Goto Function

#include "goto_function.h"

#include <util/symbol.h>

/// Return in \p dest the identifiers of the local variables declared in the \p
/// goto_function and the identifiers of the paramters of the \p goto_function.
void get_local_identifiers(
  const goto_functiont &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);

  // add parameters
  for(const auto &identifier : goto_function.parameter_identifiers)
  {
    if(!identifier.empty())
      dest.insert(identifier);
  }
}

/// Check that the goto function is well-formed
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void goto_functiont::validate(const namespacet &ns, const validation_modet vm)
  const
{
  for(const auto &identifier : parameter_identifiers)
  {
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      identifier.empty() || ns.lookup(identifier).is_parameter,
      "parameter should be marked 'is_parameter' in the symbol table",
      "affected parameter: ",
      identifier);
  }

  // function body must end with an END_FUNCTION instruction
  if(body_available())
  {
    DATA_CHECK(
      vm,
      body.instructions.back().is_end_function(),
      "last instruction should be of end function type");
  }

  body.validate(ns, vm);
}
