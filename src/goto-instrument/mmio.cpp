/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#include "mmio.h"

#include <util/options.h>

#include "nondet_volatile.h"

void mmio(goto_modelt &goto_model)
{
  // --mmio is the entry point for the memory-mapped I/O memory model. Its
  // eventual purpose is the device-memory-type-aware ordering model for the
  // weak device-memory types (ARM Device-GRE, x86 write-combining), built on
  // top of the --mm weak-memory engine; see
  // doc/architectural/mmio-weak-memory-model.md.
  //
  // For now it applies the device-environment model to all volatile accesses:
  // a read becomes non-deterministic (the device may have changed the register)
  // and a write is preserved as an observable side effect. This is the correct
  // model for the strongly-ordered device-memory types (ARM Device-nGnRnE, x86
  // uncacheable), whose accesses already occur in program order in CBMC's
  // sequential semantics. The reordering model for the weak types is future
  // work, and this is where it will be added.
  optionst options;
  options.set_option(NONDET_VOLATILE_OPT, true);
  nondet_volatile(goto_model, options);
}
