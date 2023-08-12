/*******************************************************************\

Module: JSON Commandline Interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// JSON Commandline Interface

#ifndef CPROVER_JSON_JSON_INTERFACE_H
#define CPROVER_JSON_JSON_INTERFACE_H

class cmdlinet;
class message_handlert;

/// Parses the JSON-formatted command line from stdin
///
/// Example:
/// \code{.json}
/// {
///   "arguments": [
///     "main.c"
///   ],
///   "options": {
///     "function": "foo",
///     "unwind": 3,
///     "property": [
///       "foo.assertion.1",
///       "foo.assertion.3"
///     ],
///     "trace": true,
///     "show-properties": false
///   }
/// }
/// \endcode
void json_interface(cmdlinet &, message_handlert &);

#define OPT_JSON_INTERFACE \
  "(json-ui)" \
  "(json-interface)"

#define HELP_JSON_INTERFACE                                                    \
  " {y--json-ui} \t use JSON-formatted output\n"                               \
  " {y--json-interface} \t bi-directional JSON interface\n"

#endif // CPROVER_JSON_JSON_INTERFACE_H
