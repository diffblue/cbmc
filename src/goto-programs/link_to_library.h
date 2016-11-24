/*******************************************************************\

Module: Library Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H
#define CPROVER_GOTO_PROGRAMS_LINK_TO_LIBRARY_H

#include <util/message.h>

#include "goto_model.h"

void link_to_library(
  symbol_tablet &,
  goto_functionst &,
  message_handlert &);

void link_to_library(
  goto_modelt &,
  message_handlert &);

#endif
