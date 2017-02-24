/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symtab_language.h"
#include <json/json_parser.h>
#include <util/json_symbol_table.h>

bool json_symtab_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  return parse_json(
    instream,
    path,
    get_message_handler(),
    parsed_json_file);
}

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
    error() << "json_symtab_languaget::typecheck: " << str << eom;
    return true;
  }
}

void json_symtab_languaget::show_parse(std::ostream &out)
{
  parsed_json_file.output(out);
}
