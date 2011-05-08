/*******************************************************************\

Module: Show Value Sets

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_VALUE_SETS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_VALUE_SETS_H

#include <ui_message.h>
#include <namespace.h>

#include <goto-programs/goto_functions.h>

#include "value_set_analysis.h"

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  const value_set_analysist &value_set_analysis);

void show_value_sets(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program,
  const value_set_analysist &value_set_analysis);

#endif
