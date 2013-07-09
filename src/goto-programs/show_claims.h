/*******************************************************************\

Module: Show claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_CLAIMS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_CLAIMS_H

#include <util/ui_message.h>

class goto_functionst;
class namespacet;
class goto_modelt;

void show_claims(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

void show_claims(
  const goto_modelt &,
  ui_message_handlert::uit ui);

#endif
