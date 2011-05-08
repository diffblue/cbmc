/*******************************************************************\

Module: Show program locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_LOCATIONS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_LOCATIONS_H

#include <ui_message.h>

#include <goto-programs/goto_functions.h>

void show_locations(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

#endif
