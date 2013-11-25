/*******************************************************************\

Module: Query Called Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_COMPUTE_CALLED_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_COMPUTE_CALLED_FUNCTIONS_H

#include "goto_functions.h"

// compute the set of functions whose address is taken

void compute_address_taken_functions(
  const exprt &src,
  std::set<irep_idt> &address_taken);

void compute_address_taken_functions(
  const goto_programt &goto_program,
  std::set<irep_idt> &address_taken);

void compute_address_taken_functions(
  const goto_functionst &goto_functions,
  std::set<irep_idt> &address_taken);

// computes the functions that are (potentially) called
void compute_called_functions(
  const goto_functionst &goto_functions,
  std::set<irep_idt> &functions);

#endif
