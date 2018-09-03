/*******************************************************************\

Module: Output of the verification conditions (VCCs)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the verification conditions (VCCs)

#ifndef CPROVER_GOTO_SYMEX_SHOW_VCC_H
#define CPROVER_GOTO_SYMEX_SHOW_VCC_H

#include <util/ui_message.h>

class namespacet;
class optionst;
class symex_target_equationt;

void show_vcc(
  const optionst &options,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  const namespacet &ns,
  const symex_target_equationt &equation);

#endif // CPROVER_GOTO_SYMEX_SHOW_VCC_H
