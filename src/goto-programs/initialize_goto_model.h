/*******************************************************************\

Module: Initialize a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Initialize a Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

#include <util/message.h>
#include <util/cmdline.h>

#include "goto_model.h"

bool initialize_goto_model(
  goto_modelt &goto_model,
  const cmdlinet &cmdline,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
