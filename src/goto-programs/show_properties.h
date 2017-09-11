/*******************************************************************\

Module: Show the properties

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show the properties

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H
#define CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H

#include <util/ui_message.h>

class namespacet;
class goto_modelt;

void show_properties(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H
