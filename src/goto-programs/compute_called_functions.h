/*******************************************************************\

Module: Query Called Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Query Called Functions

#ifndef CPROVER_GOTO_PROGRAMS_COMPUTE_CALLED_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_COMPUTE_CALLED_FUNCTIONS_H

#include "goto_model.h"

// compute the set of functions whose address is taken

void compute_address_taken_functions(
  const exprt &,
  std::set<irep_idt> &);

void compute_address_taken_functions(
  const goto_programt &,
  std::set<irep_idt> &);

void compute_address_taken_functions(
  const goto_functionst &,
  std::set<irep_idt> &);

// computes the functions that are (potentially) called
std::set<irep_idt> compute_called_functions(const goto_functionst &);
std::set<irep_idt> compute_called_functions(const goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_COMPUTE_CALLED_FUNCTIONS_H
