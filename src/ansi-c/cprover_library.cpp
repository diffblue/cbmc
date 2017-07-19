/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cprover_library.h"

#include <sstream>

#include <util/config.h>

#include "ansi_c_language.h"

struct cprover_library_entryt
{
  const char *function;
  const char *model;
} cprover_library[]=
#include "cprover_library.inc"
; // NOLINT(whitespace/semicolon)

std::string get_cprover_library_text(
  const std::set<irep_idt> &functions,
  const symbol_tablet &symbol_table)
{
  std::ostringstream library_text;

  library_text <<
    "#line 1 \"<builtin-library>\"\n"
    "#undef inline\n";

  if(config.ansi_c.string_abstraction)
    library_text << "#define __CPROVER_STRING_ABSTRACTION\n";

  std::size_t count=0;

  for(cprover_library_entryt *e=cprover_library;
      e->function!=nullptr;
      e++)
  {
    irep_idt id=e->function;

    if(functions.find(id)!=functions.end())
    {
      symbol_tablet::symbolst::const_iterator old=
        symbol_table.symbols.find(id);

      if(old!=symbol_table.symbols.end() &&
         old->second.value.is_nil())
      {
        count++;
        library_text << e->model << '\n';
      }
    }
  }

  if(count==0)
    return std::string();
  else
    return library_text.str();
}

void add_cprover_library(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(config.ansi_c.lib==configt::ansi_ct::libt::LIB_NONE)
    return;

  std::string library_text;

  library_text=get_cprover_library_text(functions, symbol_table);

  add_library(library_text, symbol_table, message_handler);
}

void add_library(
  const std::string &src,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(src.empty())
    return;

  std::istringstream in(src);

  ansi_c_languaget ansi_c_language;
  ansi_c_language.set_message_handler(message_handler);
  ansi_c_language.parse(in, "");

  ansi_c_language.typecheck(symbol_table, "<built-in-library>");
}
