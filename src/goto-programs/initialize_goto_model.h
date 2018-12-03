/*******************************************************************\

Module: Initialize a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Initialize a Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

#include "goto_model.h"

class message_handlert;
class optionst;

goto_modelt initialize_goto_model(
  const std::vector<std::string> &files,
  message_handlert &message_handler,
  const optionst &options);

#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
