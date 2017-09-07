/*******************************************************************\
 Module: Goto Programs
 Author: Thomas Kiley, thomas@diffblue.com
\*******************************************************************/

/// \file
/// Goto Programs Author: Thomas Kiley, thomas@diffblue.com

#include "rebuild_goto_start_function.h"

#include <goto-programs/goto_functions.h>
#include <util/language.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>
#include <langapi/mode.h>
#include <memory>

/// To rebuild the _start funciton in the event the program was compiled into
/// GOTO with a different entry function selected.
/// \param _message_handler: The message handler to report any messages with
/// \param symbol_table: The symbol table of the program (to replace the _start
///   functions symbo)
/// \param goto_functions: The goto functions of the program (to replace the
///   body of the _start function).
rebuild_goto_start_functiont::rebuild_goto_start_functiont(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions):
  messaget(_message_handler),
  symbol_table(symbol_table),
  goto_functions(goto_functions)
{
}

/// To rebuild the _start function in the event the program was compiled into
/// GOTO with a different entry function selected. It works by discarding the
/// _start symbol and GOTO function and calling on the relevant languaget to
/// generate the _start function again.
/// \param entry_function: The name of the entry function that should be
/// called from _start
/// \return Returns true if either the symbol is not found, or something went
///   wrong with generating the start_function. False otherwise.
bool rebuild_goto_start_functiont::operator()(
  const irep_idt &entry_function)
{
  const irep_idt &mode=get_entry_point_mode();

  // Get the relevant languaget to generate the new entry point with
  std::unique_ptr<languaget> language=get_language_from_mode(mode);
  INVARIANT(language, "No language found for mode: "+id2string(mode));
  language->set_message_handler(get_message_handler());

  // To create a new entry point we must first remove the old one
  remove_existing_entry_point();

  bool return_code=
    language->generate_start_function(entry_function, symbol_table);

  // Remove the function from the goto_functions so it is copied back in
  // from the symbol table during goto_convert
  if(!return_code)
  {
    const auto &start_function=
      goto_functions.function_map.find(goto_functionst::entry_point());
    if(start_function!=goto_functions.function_map.end())
    {
      goto_functions.function_map.erase(start_function);
    }
  }

  return return_code;
}

/// Find out the mode of the current entry point to determine the mode of the
/// replacement entry point
/// \return A mode string saying which language to use
irep_idt rebuild_goto_start_functiont::get_entry_point_mode() const
{
  const symbolt &current_entry_point=
    symbol_table.lookup(goto_functionst::entry_point());
  return current_entry_point.mode;
}

/// Eliminate the existing entry point function symbol and any symbols created
/// in that scope from the symbol table.
void rebuild_goto_start_functiont::remove_existing_entry_point()
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
