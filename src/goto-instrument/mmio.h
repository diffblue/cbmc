/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_MMIO_H
#define CPROVER_GOTO_INSTRUMENT_MMIO_H

class message_handlert;
class value_setst;
class goto_modelt;

void mmio(value_setst &, goto_modelt &, message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_MMIO_H
