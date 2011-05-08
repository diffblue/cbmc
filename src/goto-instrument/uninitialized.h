/*******************************************************************\

Module: Detection for Uninitialized Local Variables

Author: Daniel Kroening

Date: January 2010

\*******************************************************************/

#ifndef CPROVER_UNINITALIZED_H
#define CPROVER_UNINITALIZED_H

#include <iostream>

#include <goto-programs/goto_functions.h>

void add_uninitialized_locals_assertions(
  class contextt &context,
  goto_functionst &goto_functions);

void show_uninitialized(
  const class contextt &context,
  const goto_functionst &goto_functions,
  std::ostream &out);

#endif
