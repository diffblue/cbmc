/*******************************************************************\

Module: JSON goto_function deserialization

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// JSON goto_function deserialization

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTION_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTION_H

#include <goto-programs/goto_function.h>

class json_objectt;

/// Deserialize a goto_functiont from JSON
/// \param json: The JSON object representing a goto_function
/// \return A goto_functiont
goto_functiont goto_function_from_json(const json_objectt &json);

#endif // CPROVER_JSON_SYMTAB_LANGUAGE_JSON_GOTO_FUNCTION_H
