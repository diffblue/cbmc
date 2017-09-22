/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_MMIO_H
#define CPROVER_GOTO_INSTRUMENT_MMIO_H

class value_setst;
class goto_modelt;

void mmio(
  value_setst &,
  goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_MMIO_H
