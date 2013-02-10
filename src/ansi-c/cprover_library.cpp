/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <config.h>
#include <replace_symbol.h>

#include <linking/linking.h>

#include "cprover_library.h"
#include "ansi_c_language.h"

/*******************************************************************\

Function: add_cprover_library

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct cprover_library_entryt
{
  const char *function;
  const char *model;
} cprover_library[]=
#include "cprover_library.inc"

void add_cprover_library(
  const std::set<irep_idt> &functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  if(config.ansi_c.lib==configt::ansi_ct::LIB_NONE)
    return;

  std::ostringstream library_text;

  library_text <<
    "#line 1 \"<builtin-library>\"\n"
    "#undef inline\n";

  if(config.ansi_c.string_abstraction)
    library_text << "#define __CPROVER_STRING_ABSTRACTION\n";

  unsigned count=0;
  
  for(cprover_library_entryt *e=cprover_library;
      e->function!=NULL;
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
        library_text << e->model << std::endl;
      }
    }
  }

  if(count>0)
  {
    std::istringstream in(library_text.str());
    ansi_c_languaget ansi_c_language;
    ansi_c_language.parse(in, "", message_handler);

    symbol_tablet new_symbol_table;
    ansi_c_language.typecheck(
      new_symbol_table, "<built-in-library>", message_handler);

    linking(symbol_table, new_symbol_table, message_handler);
  }
}

