/*******************************************************************\

Module: Show the symbol table

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
#define CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H

#include <util/ui_message.h>

class goto_modelt;

void show_symbol_table(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
