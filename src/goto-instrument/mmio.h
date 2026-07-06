/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_MMIO_H
#define CPROVER_GOTO_INSTRUMENT_MMIO_H

class goto_modelt;

/// Apply the memory-mapped I/O memory model to \p goto_model. This is the entry
/// point for the \c --mmio option; see
/// doc/architectural/mmio-weak-memory-model.md.
void mmio(goto_modelt &);

#endif // CPROVER_GOTO_INSTRUMENT_MMIO_H
