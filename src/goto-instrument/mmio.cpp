/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#include "mmio.h"

void mmio(value_setst &, goto_modelt &, message_handlert &)
{
  // This used to contain a two-entry store-buffer instrumentation for MMIO
  // accesses. That code was a stale (2011) duplicate of the --mm weak-memory
  // store buffer (src/goto-instrument/wmm/), written against a shared_bufferst
  // API that no longer exists, and had been disabled (#if 0) for years. It has
  // been removed.
  //
  // Memory-mapped I/O is currently modelled by the volatile device-environment
  // pass (goto-instrument --nondet-volatile): a volatile read becomes a
  // non-deterministic value (the device may have changed the register) and a
  // volatile write is preserved as an observable side effect. An ordering-aware
  // model for the weak device-memory types is planned on top of the --mm
  // weak-memory engine, which is where the store buffer correctly belongs.
  //
  // See doc/architectural/mmio-weak-memory-model.md.
}
