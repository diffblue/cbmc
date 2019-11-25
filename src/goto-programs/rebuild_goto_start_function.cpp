/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

/// \file
/// Goto Programs Author: Thomas Kiley, thomas@diffblue.com

#include "rebuild_goto_start_function.h"

#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>
#include <util/cmdline.h>

#include <langapi/mode.h>
#include <langapi/language.h>

#include <goto-programs/goto_functions.h>

#include <memory>

std::unique_ptr<languaget> get_entry_point_language(
  const symbol_table_baset &symbol_table,
  const optionst &options,
  message_handlert &message_handler)
{
  const irep_idt &mode = get_entry_point_mode(symbol_table);

  // Get the relevant languaget to generate the new entry point with.
  std::unique_ptr<languaget> language = get_language_from_mode(mode);
  // This might fail if the driver program hasn't registered that language.
  INVARIANT(language, "No language found for mode: " + id2string(mode));
  language->set_message_handler(message_handler);
  language->set_language_options(options);
  return language;
}

const irep_idt &get_entry_point_mode(const symbol_table_baset &symbol_table)
{
  const symbolt &current_entry_point =
    symbol_table.lookup_ref(goto_functionst::entry_point());
  return current_entry_point.mode;
}

void remove_existing_entry_point(symbol_table_baset &symbol_table)
{
  // Remove the function itself
  symbol_table.remove(goto_functionst::entry_point());

  // And any symbols created in the scope of the entry point
  std::vector<irep_idt> entry_point_symbols;
  for(const auto &symbol_entry : symbol_table.symbols)
  {
    const bool is_entry_point_symbol=
      has_prefix(
        id2string(symbol_entry.first),
        id2string(goto_functionst::entry_point()));

    if(is_entry_point_symbol)
      entry_point_symbols.push_back(symbol_entry.first);
  }

  for(const irep_idt &entry_point_symbol : entry_point_symbols)
  {
    symbol_table.remove(entry_point_symbol);
  }
}
