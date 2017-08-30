/*******************************************************************\

Module: Count effective lines of code

Author: Michael Tautschnig

Date: December 2012

\*******************************************************************/

/// \file
/// Count effective lines of code

#ifndef CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H
#define CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H

#include <goto-programs/goto_functions.h>

void count_eloc(const goto_functionst &goto_functions);

void list_eloc(const goto_functionst &goto_functions);

void print_path_lengths(const goto_functionst &goto_functions);

#endif // CPROVER_GOTO_INSTRUMENT_COUNT_ELOC_H
