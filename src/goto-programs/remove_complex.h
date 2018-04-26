/*******************************************************************\

Module: Remove the 'complex' data type by compilation into structs

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

/// \file
/// Remove the 'complex' data type by compilation into structs

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_COMPLEX_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_COMPLEX_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void remove_complex(symbol_tablet &, goto_functionst &);

void remove_complex(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_COMPLEX_H
