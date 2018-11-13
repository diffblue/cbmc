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

#include <memory>

/// To rebuild the _start function in the event the program was compiled into
/// GOTO with a different entry function selected.
/// \param options: Command-line options
/// \param goto_model: The goto functions (to replace the body of the _start
///   function) and symbol table (to replace the _start function symbol) of the
///   program.
/// \param message_handler: The message handler to report any messages with
template <typename maybe_lazy_goto_modelt>
rebuild_goto_start_function_baset<maybe_lazy_goto_modelt>::
  rebuild_goto_start_function_baset(
    const optionst &options,
    maybe_lazy_goto_modelt &goto_model,
    message_handlert &message_handler)
  : messaget(message_handler), options(options), goto_model(goto_model)
{
}

/// To rebuild the _start function in the event the program was compiled into
/// GOTO with a different entry function selected. It works by discarding the
/// _start symbol and GOTO function and calling on the relevant languaget to
/// generate the _start function again.
/// \return Returns true if either the symbol is not found, or something went
///   wrong with generating the start_function. False otherwise.
template<typename maybe_lazy_goto_modelt>
bool rebuild_goto_start_function_baset<maybe_lazy_goto_modelt>::operator()()
{
  const irep_idt &mode=get_entry_point_mode();

  // Get the relevant languaget to generate the new entry point with
  std::unique_ptr<languaget> language=get_language_from_mode(mode);
  INVARIANT(language, "No language found for mode: "+id2string(mode));
  language->set_message_handler(get_message_handler());
  language->set_language_options(options);

  // To create a new entry point we must first remove the old one
  remove_existing_entry_point();

  bool return_code=
    language->generate_support_functions(goto_model.symbol_table);

  // Remove the function from the goto functions so it is copied back in
  // from the symbol table during goto_convert
  if(!return_code)
    goto_model.unload(goto_functionst::entry_point());

  return return_code;
}

/// Find out the mode of the current entry point to determine the mode of the
/// replacement entry point
/// \return A mode string saying which language to use
template<typename maybe_lazy_goto_modelt>
irep_idt rebuild_goto_start_function_baset<maybe_lazy_goto_modelt>::
get_entry_point_mode() const
{
  const symbolt &current_entry_point=
    *goto_model.symbol_table.lookup(goto_functionst::entry_point());
  return current_entry_point.mode;
}

/// Eliminate the existing entry point function symbol and any symbols created
/// in that scope from the symbol table.
template<typename maybe_lazy_goto_modelt>
void rebuild_goto_start_function_baset<maybe_lazy_goto_modelt>::
remove_existing_entry_point()
{
  // Remove the function itself
  goto_model.symbol_table.remove(goto_functionst::entry_point());

  // And any symbols created in the scope of the entry point
  std::vector<irep_idt> entry_point_symbols;
  for(const auto &symbol_entry : goto_model.symbol_table.symbols)
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
    goto_model.symbol_table.remove(entry_point_symbol);
  }
}

template class rebuild_goto_start_function_baset<goto_modelt>;
template class rebuild_goto_start_function_baset<lazy_goto_modelt>;
