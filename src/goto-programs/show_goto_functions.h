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
  " --show-goto-functions        show goto program\n" \
  " --list-goto-functions        list goto functions\n"
// clang-format on

void show_goto_functions(
  const namespacet &ns,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  bool list_only = false);

void show_goto_functions(
  const goto_modelt &,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  bool list_only = false);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H
