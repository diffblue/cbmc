/*******************************************************************\
 Module: Goto Programs
 Author: Thomas Kiley, thomas@diffblue.com
\*******************************************************************/

#include "rebuild_goto_start_function.h"
#include <util/language.h>
#include <util/symbol.h>
#include <langapi/mode.h>
#include <memory>

/*******************************************************************\

Function: rebuild_goto_start_functiont::rebuild_goto_start_functiont

  Inputs:
          _message_handler - The message handler to report any messages with
          symbol_table - The symbol table of the program (to replace the
                         _start functions symbo)
          goto_functions - The goto functions of the program (to replace the
                           body of the _start function).

 Outputs:

 Purpose: To rebuild the _start funciton in the event the program was
          compiled into GOTO with a different entry function selected.

\*******************************************************************/

rebuild_goto_start_functiont::rebuild_goto_start_functiont(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions):
  messaget(_message_handler),
  symbol_table(symbol_table),
  goto_functions(goto_functions)
{
}

/*******************************************************************\

Function: rebuild_goto_start_functiont::operator()

  Inputs:
          entry_function - The name of the entry function that should be
                           called from _start

 Outputs: Returns true if either the symbol is not found, or something went
          wrong with generating the start_function. False otherwise.

 Purpose: To rebuild the _start function in the event the program was
          compiled into GOTO with a different entry function selected.
          It works by discarding the _start symbol and GOTO function
          and calling on the relevant languaget to generate the _start
          function again.

\*******************************************************************/

bool rebuild_goto_start_functiont::operator()(const irep_idt &entry_function)
{
  const auto &desired_entry_function=
    symbol_table.symbols.find(entry_function);

  // Check the specified entry function is a function in the symbol table
  if(desired_entry_function==symbol_table.symbols.end())
  {
    error() << "main symbol `" << entry_function
            << "' not found" << eom;
    return true;
  }

  // Remove the existing _start function so we can create a new one
  symbol_table.remove(ID__start);

  auto language=
    std::unique_ptr<languaget>(
      get_language_from_mode(
        desired_entry_function->second.mode));
  assert(language);

  bool return_code=
    language->generate_start_function(
      desired_entry_function->second,
      symbol_table);

  // Remove the function from the goto_functions so is copied back in
  // from the symbol table during goto_convert
  if(!return_code)
  {
    const auto &start_function=goto_functions.function_map.find(ID__start);
    if(start_function!=goto_functions.function_map.end())
    {
      goto_functions.function_map.erase(start_function);
    }
  }

  return return_code;
}
