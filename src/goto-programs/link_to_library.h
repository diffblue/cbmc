/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
#define CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H

#include <util/message.h>

#include "goto_functions.h"

void link_to_library(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler);

#endif
