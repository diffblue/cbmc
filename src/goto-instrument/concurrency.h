/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Encoding for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H
#define CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H

class goto_modelt;
class value_setst;

void concurrency(value_setst &, goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H
