/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation

#ifndef CPROVER_GOTO_PROGRAMS_MM_IO_H
#define CPROVER_GOTO_PROGRAMS_MM_IO_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void mm_io(const symbol_tablet &, goto_functionst &);
void mm_io(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_MM_IO_H
