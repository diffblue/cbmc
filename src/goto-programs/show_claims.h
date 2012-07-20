/*******************************************************************\

Module: Show claims

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SHOW_CLAIMS_H
#define CPROVER_GOTO_PROGRAMS_SHOW_CLAIMS_H

#include <ui_message.h>

class goto_functionst;
class namespacet;

void show_claims(
  const namespacet &ns,
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions);

#endif
