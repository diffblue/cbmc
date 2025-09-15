/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#ifndef CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
#define CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H

#include <list>
#include <string>

#include <util/irep.h>

class goto_modelt;
class message_handlert;

void remove_function(
  goto_modelt &,
  const irep_idt &identifier,
  message_handlert &);

void remove_functions(
  goto_modelt &,
  const std::list<std::string> &names,
  message_handlert &);

/// Remove functions matching any of the provided regular expression patterns.
/// \param goto_model: The goto model to modify
/// \param pattern: Regex patterns to match function names against
/// \param message_handler: For status/warning/error messages
void remove_functions_regex(
  goto_modelt &goto_model,
  const std::string &pattern,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
