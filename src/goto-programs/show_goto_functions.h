/*******************************************************************\

Module: Show the goto functions

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Show the goto functions

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H

#include <util/ui_message.h>

class namespacet;
class goto_modelt;
class goto_functionst;

// clang-format off
#define OPT_SHOW_GOTO_FUNCTIONS \
  "(show-goto-functions)" \
  "(list-goto-functions)"

#define HELP_SHOW_GOTO_FUNCTIONS \
  " --show-goto-functions        show loaded goto program\n" \
  " --list-goto-functions        list loaded goto functions\n"
// clang-format on

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert &ui_message_handler,
  const goto_functionst &goto_functions,
  bool list_only);

void show_goto_functions(
  const goto_modelt &,
  ui_message_handlert &ui_message_handler,
  bool list_only);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H
