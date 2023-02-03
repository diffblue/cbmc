/*******************************************************************\

Module: Show the symbol table

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the symbol table

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
#define CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H

class goto_modelt;
class symbol_table_baset;
class ui_message_handlert;

void show_symbol_table(const symbol_table_baset &, ui_message_handlert &ui);

void show_symbol_table_brief(
  const symbol_table_baset &,
  ui_message_handlert &ui);

void show_symbol_table(
  const goto_modelt &,
  ui_message_handlert &ui);

void show_symbol_table_brief(
  const goto_modelt &,
  ui_message_handlert &ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
