/*******************************************************************\

Module: JSON goto_functions deserialization

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// JSON goto_functions deserialization

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTIONS_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTIONS_H

class goto_functionst;
class jsont;

/// Deserialize goto_functionst from JSON
/// \param json: The JSON object representing goto_functions
/// \param goto_functions: The goto_functionst object to populate
void goto_functions_from_json(
  const jsont &json,
  goto_functionst &goto_functions);

#endif // CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTIONS_H
