/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
#define CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H

#include <options.h>
#include <message.h>

#include "goto_functions.h"

void link_to_library(
  contextt &context,
  goto_functionst &goto_functions,
  const optionst &options,
  message_handlert &message_handler);

#endif
