/*******************************************************************\

Module: Remove the 'vector' data type by compilation into arrays

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

/// \file
/// Remove the 'vector' data type by compilation into arrays

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_VECTOR_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_VECTOR_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void remove_vector(symbol_tablet &, goto_functionst &);

void remove_vector(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_VECTOR_H
