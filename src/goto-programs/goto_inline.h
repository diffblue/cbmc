/*******************************************************************\

Module: Function Inlining

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INLINE_H
#define CPROVER_GOTO_INLINE_H

#include <util/message_stream.h>

#include "goto_functions.h"

// do a full inlining
void goto_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler);

// inline those functions marked as "inlined"
// and functions with less than _smallfunc_limit instructions
void goto_partial_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  unsigned _smallfunc_limit = 0);

#endif
