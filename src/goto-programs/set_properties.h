/*******************************************************************\

Module: Set the properties to check

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Set the properties to check

#ifndef CPROVER_GOTO_PROGRAMS_SET_PROPERTIES_H
#define CPROVER_GOTO_PROGRAMS_SET_PROPERTIES_H

#include <list>
#include <string>

class goto_functionst;
class goto_modelt;
class goto_programt;

void set_properties(
  goto_functionst &goto_functions,
  const std::list<std::string> &properties);

void set_properties(
  goto_modelt &goto_model,
  const std::list<std::string> &properties);

void label_properties(goto_functionst &);
void label_properties(goto_programt &);
void label_properties(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_SET_PROPERTIES_H
