/*******************************************************************\

Module: Show the properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H
#define CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H

#include <util/ui_message.h>

class goto_functionst;
class namespacet;
class goto_modelt;

void show_properties(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

void show_properties(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif
