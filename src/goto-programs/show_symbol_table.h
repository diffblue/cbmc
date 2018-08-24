/*******************************************************************\

Module: Show the symbol table

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the symbol table

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
#define CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H

#include <util/ui_message.h>

class symbol_tablet;
class goto_modelt;

void show_symbol_table(
  const symbol_tablet &,
  ui_message_handlert &ui);

void show_symbol_table_brief(
  const symbol_tablet &,
  ui_message_handlert &ui);

void show_symbol_table(
  const goto_modelt &,
  ui_message_handlert &ui);

void show_symbol_table_brief(
  const goto_modelt &,
  ui_message_handlert &ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
