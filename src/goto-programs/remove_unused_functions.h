/*******************************************************************\

Module: Unused function removal

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Unused function removal

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_UNUSED_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_UNUSED_FUNCTIONS_H

#include <util/message.h>

#include <goto-programs/goto_model.h>

void remove_unused_functions(
  goto_functionst &,
  message_handlert &);

void remove_unused_functions(
  goto_modelt &,
  message_handlert &);

void find_used_functions(
  const irep_idt &current,
  goto_functionst &functions,
  id_sett &seen);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_UNUSED_FUNCTIONS_H
