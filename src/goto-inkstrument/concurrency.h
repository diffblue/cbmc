/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Encoding for Threaded Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H
#define CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H

#include <pointer-analysis/value_sets.h>
#include <goto-programs/goto_model.h>

void concurrency(value_setst &, goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_CONCURRENCY_H
