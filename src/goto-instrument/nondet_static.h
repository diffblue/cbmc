/*******************************************************************\

Module: Nondeterministic initialization of certain global scope
        variables

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Nondeterministic initialization of certain global scope variables

#ifndef CPROVER_GOTO_INSTRUMENT_NONDET_STATIC_H
#define CPROVER_GOTO_INSTRUMENT_NONDET_STATIC_H

class goto_functionst;
class namespacet;
class goto_modelt;

void nondet_static(
  const namespacet &,
  goto_functionst &);

void nondet_static(goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_NONDET_STATIC_H
