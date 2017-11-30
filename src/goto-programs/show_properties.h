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
class symbol_tablet;
class goto_functionst;

void show_properties(
  const goto_modelt &,
  ui_message_handlert::uit ui);

void show_properties(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

/// \brief Returns a source_locationt that corresponds
/// to the property given by an irep_idt.
/// \param property irep_idt and goto_functions
source_locationt find_property(
    const irep_idt &property,
    const goto_functionst &);

#endif // CPROVER_GOTO_PROGRAMS_SHOW_PROPERTIES_H
