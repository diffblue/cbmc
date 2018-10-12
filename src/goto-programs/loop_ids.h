/*******************************************************************\

Module: Loop IDs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Loop IDs

#ifndef CPROVER_GOTO_PROGRAMS_LOOP_IDS_H
#define CPROVER_GOTO_PROGRAMS_LOOP_IDS_H

#include <util/ui_message.h>

#include "goto_model.h"

void show_loop_ids(
  ui_message_handlert::uit,
  const goto_modelt &);

void show_loop_ids(
  ui_message_handlert::uit,
  const goto_functionst &);

void show_loop_ids(
  ui_message_handlert::uit,
  const irep_idt &function_identifier,
  const goto_programt &);

#endif // CPROVER_GOTO_PROGRAMS_LOOP_IDS_H
