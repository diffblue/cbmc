/*******************************************************************\

Module: Show program locations

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Show program locations

#ifndef CPROVER_GOTO_INSTRUMENT_SHOW_LOCATIONS_H
#define CPROVER_GOTO_INSTRUMENT_SHOW_LOCATIONS_H

#include <util/ui_message.h>

class goto_modelt;

void show_locations(
  ui_message_handlert::uit ui,
  const goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_SHOW_LOCATIONS_H
