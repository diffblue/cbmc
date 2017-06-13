/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H

class goto_functionst;
class namespacet;

void slice_global_inits(
  const namespacet &ns,
  goto_functionst &goto_functions);

#endif
