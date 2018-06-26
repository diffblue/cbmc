/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symtab_language.h"
#include <json/json_parser.h>
#include <util/json_symbol_table.h>
#include <util/namespace.h>

/// Parse a goto program in json form.
/// \param instream: The input stream
/// \param path: A file path
/// \return: boolean signifying success or failure of the parsing
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
    follow_type_symbols(symbol_table);
    return false;
  }
  catch(const std::string &str)
  {
    error() << "json_symtab_languaget::typecheck: " << str << eom;
    return true;
  }
}

/// Follow type symbols present in the irep using the passed irep
/// as the root for this operation.
/// \param irep: An irep `irep` to use as a root for the recursive following.
/// \param ns: The namespace to use for symbol following.
void json_symtab_languaget::follow_type_symbols(
  irept &irep,
  const namespacet &ns)
{
  ns.follow_type_symbol(irep);

  for(irept &sub : irep.get_sub())
  {
    follow_type_symbols(sub, ns);
  }

  for(auto &entry : irep.get_named_sub())
  {
    irept &sub = entry.second;

    follow_type_symbols(sub, ns);
  }
}

/// Follow type symbols present in every symbol in the symbol table.
/// \param symbol_table: The symbol table `symbol_table` that has been produced as part
///                      of the parsing and the typechecking of the goto program in json
///                      form.
void json_symtab_languaget::follow_type_symbols(symbol_tablet &symbol_table)
{
  const namespacet ns(symbol_table);

  std::vector<irep_idt> type_symbol_names;

  for(auto &entry : symbol_table)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(entry.first);

    if(symbol.is_type)
    {
      type_symbol_names.push_back(symbol.name);
    }

    // Modify entries in place
    follow_type_symbols(symbol.type, ns);
    follow_type_symbols(symbol.value, ns);
  }

  for(const irep_idt &id : type_symbol_names)
  {
    symbol_table.remove(id);
  }
}

/// Output the result of the parsed json file to the output stream
/// passed as a parameter to this function.
/// \param out: The stream to use to output the parsed_json_file.
void json_symtab_languaget::show_parse(std::ostream &out)
{
  parsed_json_file.output(out);
}
