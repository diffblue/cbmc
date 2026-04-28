/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

void cpp_typecheckt::convert(cpp_linkage_spect &linkage_spec)
{
  irep_idt old_linkage_spec = current_linkage_spec;

  current_linkage_spec = linkage_spec.linkage().get(ID_value);

  // there is a linkage spec "C++", which we know as "cpp"
  if(current_linkage_spec == "C++")
    current_linkage_spec = ID_cpp;

  // do the declarations
  for(auto it = linkage_spec.items().begin(); it != linkage_spec.items().end();
      it++)
  {
    const std::size_t errors_before =
      get_message_handler().get_message_count(messaget::M_ERROR);
    try
    {
      convert(*it);
    }
    catch(int)
    {
      // Continue processing remaining items so that later
      // declarations (e.g., forward declarations, typedefs)
      // are still registered in the symbol table.
      // Restore the error count: the failed item's error was
      // already reported but should not cause a hard failure
      // of the entire translation unit.
      get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
    }
  }

  // back to previous linkage spec
  current_linkage_spec = old_linkage_spec;
}
