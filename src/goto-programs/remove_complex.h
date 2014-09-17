/*******************************************************************\

Module: Remove the 'complex' data type by compilation into structs

Author: Daniel Kroening

Date:   September 2014

\*******************************************************************/

#ifndef CPROVER_COMPLEX_H
#define CPROVER_COMPLEX_H

#include <goto-programs/goto_model.h>

void remove_complex(symbol_tablet &, goto_functionst &);

void remove_complex(goto_modelt &);

#endif
