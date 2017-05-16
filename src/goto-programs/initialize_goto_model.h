/*******************************************************************\

Module: Initialize a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

#include <util/message.h>
#include <util/cmdline.h>

#include "goto_model.h"


bool initialize_goto_model(
  goto_modelt &goto_model,
  const cmdlinet & cmdline,
  bool generate_start_function,
  message_handlert &message_handler);

inline bool initialize_goto_model(
  goto_modelt &goto_model,
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  return initialize_goto_model(goto_model, cmdline, true, message_handler);
}


#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
