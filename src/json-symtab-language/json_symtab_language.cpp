/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symtab_language.h"

#include <util/symbol_table.h>

#include <json/json_parser.h>
#include <linking/linking.h>

#include "json_symbol_table.h"

/// Parse a goto program in json form.
/// \param instream: The input stream
/// \param path: A file path
/// \param message_handler: A message handler
/// \return boolean signifying success or failure of the parsing
bool json_symtab_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  return parse_json(instream, path, message_handler, parsed_json_file);
}

/// Typecheck a goto program in json form.
/// \param symbol_table: The symbol table containing symbols read from file.
/// \param module: A useless parameter, there for interface consistency.
/// \param message_handler: A message handler
/// \return boolean signifying success or failure of the typechecking.
bool json_symtab_languaget::typecheck(
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  (void)module; // unused parameter

  symbol_tablet new_symbol_table;

  try
  {
    symbol_table_from_json(parsed_json_file, new_symbol_table);
    return linking(symbol_table, new_symbol_table, message_handler);
  }
  catch(const std::string &str)
  {
    messaget log(message_handler);
    log.error() << "typecheck: " << str << messaget::eom;
    return true;
  }
}

/// Output the result of the parsed json file to the output stream
/// passed as a parameter to this function.
/// \param out: The stream to use to output the parsed_json_file.
/// \param message_handler: A message handler
void json_symtab_languaget::show_parse(
  std::ostream &out,
  message_handlert &message_handler)
{
  (void)message_handler;
  parsed_json_file.output(out);
}
