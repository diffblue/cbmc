/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_CALL_SEQUENCES_H
#define CPROVER_GOTO_INSTRUMENT_CALL_SEQUENCES_H

class goto_modelt;

void show_call_sequences(const goto_modelt &);
void check_call_sequence(const goto_modelt &);
void list_calls_and_arguments(const goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_CALL_SEQUENCES_H
