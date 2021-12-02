/*******************************************************************\

Module: Checks for Errors in C and Java Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Checks for Errors in C and Java Programs

#ifndef CPROVER_ANALYSES_GOTO_CHECK_H
#define CPROVER_ANALYSES_GOTO_CHECK_H

#include <goto-programs/goto_functions.h>

class goto_modelt;
class namespacet;
class optionst;
class message_handlert;

void goto_check(
  const namespacet &,
  const optionst &,
  goto_functionst &,
  message_handlert &);

void goto_check(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &,
  const namespacet &,
  const optionst &,
  message_handlert &);

void goto_check(
  const optionst &,
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_ANALYSES_GOTO_CHECK_H
