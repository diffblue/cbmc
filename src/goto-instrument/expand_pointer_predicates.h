/*******************************************************************\

Module: Expand pointer predicates in assertions/assumptions.

Author: Klaas Pruiksma

Date: June 2018

\*******************************************************************/

/// \file
/// Replace pointer predicates (e.g. __CPROVER_points_to_valid_memory)
/// in assumptions and assertions with suitable expressions and additional
/// instructions.

#ifndef CPROVER_GOTO_INSTRUMENT_EXPAND_POINTER_PREDICATES_H
#define CPROVER_GOTO_INSTRUMENT_EXPAND_POINTER_PREDICATES_H

class goto_modelt;

void expand_pointer_predicates(goto_modelt &goto_model);

#endif // CPROVER_GOTO_INSTRUMENT_EXPAND_POINTER_PREDICATES_H
