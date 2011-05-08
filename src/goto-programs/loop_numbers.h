/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CBMC_LOOP_IDS_H
#define CPROVER_CBMC_LOOP_IDS_H

#include <ui_message.h>

#include "goto_functions.h"

void show_loop_numbers(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

void show_loop_numbers(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program);

#endif
