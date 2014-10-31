/*******************************************************************\

Module: Remove the 'vector' data type by compilation into arrays

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_VECTOR_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_VECTOR_H

#include <goto-programs/goto_model.h>

void remove_vector(symbol_tablet &, goto_functionst &);

void remove_vector(goto_modelt &);

#endif
