/*******************************************************************\

Module: Show the goto functions

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_GOTO_FUNCTIONS_H

#include <util/ui_message.h>

class goto_functionst;
class namespacet;
class goto_modelt;

void show_goto_functions(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

void show_goto_functions(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif
