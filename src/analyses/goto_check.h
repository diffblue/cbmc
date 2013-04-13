/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CHECK_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CHECK_H

#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_functions.h>

void goto_check(
  const namespacet &ns,
  const optionst &options,
  goto_functionst &goto_functions);

#endif
