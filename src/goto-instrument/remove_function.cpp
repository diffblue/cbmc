/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#include "remove_function.h"

#include <util/message.h>

#include <goto-programs/goto_model.h>

#include <regex>

/// Remove the body of function "identifier" such that an analysis will treat it
/// as a side-effect free function with non-deterministic return value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_model  Input program to be modified
/// identifier  Function to be removed
/// message_handler  Error/status output
void remove_function(
  goto_modelt &goto_model,
  const irep_idt &identifier,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  goto_functionst::function_mapt::iterator entry=
    goto_model.goto_functions.function_map.find(identifier);

  if(entry==goto_model.goto_functions.function_map.end())
  {
    message.error() << "No function " << identifier
                    << " in goto program" << messaget::eom;
    return;
  }
  else if(to_code_type(goto_model.symbol_table.lookup_ref(identifier).type)
            .get_inlined())
  {
    message.warning() << "Function " << identifier << " is inlined, "
                      << "instantiations will not be removed"
                      << messaget::eom;
  }

  if(entry->second.body_available())
  {
    message.status() << "Removing body of " << identifier
                     << messaget::eom;
    entry->second.clear();
    symbolt &symbol = goto_model.symbol_table.get_writeable_ref(identifier);
    symbol.value.make_nil();
    symbol.is_file_local = false;
  }
}

/// Remove the body of all functions listed in "names" such that an analysis
/// will treat it as a side-effect free function with non-deterministic return
/// value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_model  Input program to be modified
/// names  List of functions to be removed
/// message_handler  Error/status output
void remove_functions(
  goto_modelt &goto_model,
  const std::list<std::string> &names,
  message_handlert &message_handler)
{
  for(const auto &f : names)
    remove_function(goto_model, f, message_handler);
}

/// Remove functions matching a regular expression pattern
/// \param goto_model: The goto model to modify
/// \param pattern: The regex pattern to match function names against
/// \param pattern_as_str: The string representation of \p pattern
/// \param message_handler: For status/warning/error messages
static void remove_functions_regex(
  goto_modelt &goto_model,
  const std::regex &pattern,
  const std::string &pattern_as_str,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  message.debug() << "Removing functions matching pattern: " << pattern_as_str
                  << messaget::eom;

  // Collect matching function names first to avoid modifying the map while
  // iterating
  std::list<irep_idt> matching_functions;

  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    const std::string &function_name = id2string(entry.first);
    if(std::regex_match(function_name, pattern))
    {
      matching_functions.push_back(entry.first);
    }
  }

  // Now remove all matching functions
  for(const auto &func : matching_functions)
  {
    remove_function(goto_model, func, message_handler);
  }

  message.debug() << "Removed " << matching_functions.size()
                  << " function(s) matching pattern: " << pattern_as_str
                  << messaget::eom;
}

void remove_functions_regex(
  goto_modelt &goto_model,
  const std::string &pattern,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  try
  {
    std::regex regex_pattern{pattern};

    remove_functions_regex(goto_model, regex_pattern, pattern, message_handler);
  }
  catch(const std::regex_error &e)
  {
    message.error() << "Invalid regular expression pattern: " << pattern << " ("
                    << e.what() << ")" << messaget::eom;
  }
}
