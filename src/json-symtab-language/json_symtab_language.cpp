/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symtab_language.h"
#include "json_symbol_table.h"
#include <json/json_parser.h>
#include <util/namespace.h>

/// Parse a goto program in json form.
/// \param instream: The input stream
/// \param path: A file path
/// \return: boolean signifying success or failure of the parsing
bool json_symtab_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  return parse_json(instream, path, get_message_handler(), parsed_json_file);
}

/// Typecheck a goto program in json form.
/// \param symbol_table: The symbol table containing symbols read from file.
/// \param module: A useless parameter, there for interface consistency.
/// \return: boolean signifying success or failure of the typechecking.
bool json_symtab_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  try
  {
    symbol_table_from_json(parsed_json_file, symbol_table);
    return false;
  }
  catch(const std::string &str)
  {
    error() << "typecheck: " << str << eom;
    return true;
  }
}

/// Output the result of the parsed json file to the output stream
/// passed as a parameter to this function.
/// \param out: The stream to use to output the parsed_json_file.
void json_symtab_languaget::show_parse(std::ostream &out)
{
  parsed_json_file.output(out);
}
