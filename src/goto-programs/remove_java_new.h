// Copyright 2017 Diffblue Limited. All Rights Reserved.

/// \file
/// Function-level/module-level pass to remove java_new and replace with
/// malloc & zero-initialize

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_JAVA_NEW_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_JAVA_NEW_H

#include "goto_model.h"
#include <util/message.h>

bool remove_java_new(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns,
  message_handlert &message_handler);

void remove_java_new(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler);

void remove_java_new(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_JAVA_NEW_H
