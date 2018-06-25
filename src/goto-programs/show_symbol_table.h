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
class symbolt;
class cmdlinet;

// clang-format off
#define OPT_SHOW_SYMBOL_TABLE \
  "(show-symbol-table)" \
  "(list-symbols)(list-symbol-table)" \
  "(filter-symbol-table):"

#define HELP_SHOW_SYMBOL_TABLE \
  " --show-symbol-table          show loaded symbol table\n" \
  " --list-symbols               keept for compatibility, use --list-symbol-table instead\n" \
  " --list-symbol-table          list symbols with type information\n" \
  " --filter-symbol-table        filter the symbol table for passed flags before printing\n" \
  "                              Allowed flags are: lvalue, static_lifetime, thread_local,\n" \
  "                              type, extern, intern, output, macro, parameter, auxilary,\n" \
  "                              You might pass a comma separatd list flag1,flag2,...\n"
// clang-format on

class symbol_table_filtert
{
public:
  symbol_table_filtert();
  virtual bool is_selected(const symbolt &symbol) const;
  virtual bool setup(const std::string &flags);

protected:
  virtual bool set_filter_flag(const std::string &flag);

private:
  bool filter_lvalue;
  bool filter_static_lifetime;
  bool filter_thread_local;
  bool filter_file_local;
  bool filter_type;
  bool filter_extern;
  bool filter_input;
  bool filter_output;
  bool filter_macro;
  bool filter_parameter;
  bool filter_auxilary;
  bool filter_weak;
  bool filter_property;
  bool filter_state_var;
  bool filter_exported;
  bool filter_volatile;
  bool default_pass;
};

bool check_commandline_for_show_symbol_flags(
  int &return_value,
  const cmdlinet &cmdline,
  const goto_modelt &goto_model,
  ui_message_handlert::uit ui);

void show_symbol_table(const symbol_tablet &, ui_message_handlert::uit ui);

void show_symbol_table(
  const symbol_tablet &,
  const symbol_table_filtert &,
  ui_message_handlert::uit ui);

void show_symbol_table_brief(
  const symbol_tablet &,
  ui_message_handlert::uit ui);

void show_symbol_table_brief(
  const symbol_tablet &,
  const symbol_table_filtert &,
  ui_message_handlert::uit ui);

void show_symbol_table(const goto_modelt &, ui_message_handlert::uit ui);

void show_symbol_table(
  const goto_modelt &,
  const symbol_table_filtert &,
  ui_message_handlert::uit ui);

void show_symbol_table_brief(
  const goto_modelt &,
  const symbol_table_filtert &,
  ui_message_handlert::uit ui);

void show_symbol_table_brief(const goto_modelt &, ui_message_handlert::uit ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_SYMBOL_TABLE_H
