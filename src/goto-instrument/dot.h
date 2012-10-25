/*******************************************************************\

Module: Dump Goto-Program as DOT Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DOT_H
#define CPROVER_DOT_H

#include <goto-programs/goto_functions.h>

void dot(
  const goto_functionst &src,
  const namespacet &ns,
  std::ostream &out);

#endif
