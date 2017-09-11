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

#define OPT_SHOW_GOTO_FUNCTIONS \
  "(show-goto-functions)"

#define HELP_SHOW_GOTO_FUNCTIONS \
  " --show-goto-functions        show goto program\n"

void show_goto_functions(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H
