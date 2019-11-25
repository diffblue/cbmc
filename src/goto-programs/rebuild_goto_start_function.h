/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas@diffblue.com

\*******************************************************************/

/// \file
/// Goto Programs Author: Thomas Kiley, thomas@diffblue.com

#ifndef CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H

#include <memory>

#include <util/irep.h>

class languaget;
class message_handlert;
class optionst;
class symbol_table_baset;

#define OPT_FUNCTIONS \
  "(function):"

#define HELP_FUNCTIONS \
  " --function name              set main function name\n"

/// Eliminate the existing entry point function symbol and any symbols created
/// in that scope from the \p symbol_table.
void remove_existing_entry_point(symbol_table_baset &);

/// Find out the mode of the current entry point to determine the mode of the
/// replacement entry point
/// \return A mode string saying which language to use
const irep_idt &get_entry_point_mode(const symbol_table_baset &);

/// Find the language corresponding to the __CPROVER_start function
/// \param symbol_table: The symbol table of the goto model.
/// \param options: Command-line options
/// \param message_handler: The message handler to report any messages with
std::unique_ptr<languaget> get_entry_point_language(
  const symbol_table_baset &symbol_table,
  const optionst &options,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_REBUILD_GOTO_START_FUNCTION_H
