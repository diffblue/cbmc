/*******************************************************************\

Module: JSON symbol table language. Accepts a JSON format symbol
        table that has been produced out-of-process, e.g. by using
        a compiler's front-end.

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symtab_language.h"

bool json_symtab_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  return true;
}

bool json_symtab_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  return true;
}

void json_symtab_languaget::show_parse(std::ostream &out)
{
}
