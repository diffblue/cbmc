/*******************************************************************\

Module: Set the properties to check

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SET_PROPERTIES_H
#define CPROVER_GOTO_PROGRAMS_SET_PROPERTIES_H

#include <goto-programs/goto_functions.h>

void set_properties(
  goto_functionst &goto_functions,
  const std::list<std::string> &properties);

void make_assertions_false(goto_functionst &);  

void label_properties(goto_functionst &);
void label_properties(goto_programt &);

#endif
