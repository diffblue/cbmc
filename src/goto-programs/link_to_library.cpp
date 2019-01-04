/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Library Linking

#include "link_to_library.h"

#include "compute_called_functions.h"
#include "goto_convert_functions.h"

/// Complete missing function definitions using the \p library.
/// \param goto_model: goto model that may contain function calls and symbols
///   with missing function bodies
/// \param message_handler: message handler to report library processing
///   problems
/// \param library: generator function that produces function definitions for a
///   given set of symbol names that have no body.
void link_to_library(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const std::function<
    void(const std::set<irep_idt> &, symbol_tablet &, message_handlert &)>
    &library)
{
  link_to_library(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler,
    library);
}

/// Complete missing function definitions using the \p library.
/// \param symbol_table: symbol table that may contain symbols with missing
///   function bodies
/// \param goto_functions: goto functions that may contain function calls with
///   missing function bodies
/// \param message_handler: message handler to report library processing
///   problems
/// \param library: generator function that produces function definitions for a
///   given set of symbol names that have no body.
void link_to_library(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler,
  const std::function<
    void(const std::set<irep_idt> &, symbol_tablet &, message_handlert &)>
    &library)
{
  // this needs a fixedpoint, as library functions
  // may depend on other library functions

  std::set<irep_idt> added_functions;

  while(true)
  {
    std::unordered_set<irep_idt> called_functions =
      compute_called_functions(goto_functions);

    // eliminate those for which we already have a body

    std::set<irep_idt> missing_functions;

    for(const auto &id : called_functions)
    {
      goto_functionst::function_mapt::const_iterator
        f_it=goto_functions.function_map.find(id);

      if(f_it!=goto_functions.function_map.end() &&
         f_it->second.body_available())
      {
        // it's overridden!
      }
      else if(added_functions.find(id)!=added_functions.end())
      {
        // already added
      }
      else
        missing_functions.insert(id);
    }

    // done?
    if(missing_functions.empty())
      break;

    library(missing_functions, symbol_table, message_handler);

    // convert to CFG
    for(const auto &id : missing_functions)
    {
      if(symbol_table.symbols.find(id)!=symbol_table.symbols.end())
        goto_convert(id, symbol_table, goto_functions, message_handler);

      added_functions.insert(id);
    }
  }
}
