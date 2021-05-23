/*******************************************************************\

Module: Function Inlining

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Inlining
/// This gives a number of different interfaces to the function
/// inlining functionality of goto_inlinet.

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_INLINE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_INLINE_H

#include <util/json.h>

class goto_functionst;
class goto_modelt;
class message_handlert;
class namespacet;

// do a full inlining

void goto_inline(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool adjust_function=false);

void goto_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  bool adjust_function=false);

// inline those functions marked as "inlined" and functions with less
// than _smallfunc_limit instructions

void goto_partial_inline(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  unsigned smallfunc_limit=0,
  bool adjust_function=false);

void goto_partial_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  unsigned smallfunc_limit=0,
  bool adjust_function=false);

// transitively inline all calls the given function makes

void goto_function_inline(
  goto_modelt &goto_model,
  const irep_idt function,
  message_handlert &message_handler,
  bool adjust_function=false,
  bool caching=true);

void goto_function_inline(
  goto_functionst &goto_functions,
  const irep_idt function,
  const namespacet &ns,
  message_handlert &message_handler,
  bool adjust_function=false,
  bool caching=true);

jsont goto_function_inline_and_log(
  goto_modelt &,
  const irep_idt function,
  message_handlert &message_handler,
  bool adjust_function=false,
  bool caching=true);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_INLINE_H
