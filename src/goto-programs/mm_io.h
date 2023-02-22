/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation
///
/// \details
/// In the case where a modelling function named `__CPROVER_mm_io_r` exists in
/// the symbol table, this pass will insert calls to this function before
/// pointer dereference reads. Only the case where there is a single dereference
/// on the right hand side of an assignment is included in the set of
/// dereference reads.
///
/// In the case where a modelling function named
/// `__CPROVER_mm_io_w` exists in the symbol table, this pass will insert calls
/// to this function before all pointer dereference writes. All pointer
/// dereference writes are assumed to be on the left hand side of assignments.
///
/// For details as to how and why this is used see the "Device behavior" section
/// of modeling-mmio.md

#ifndef CPROVER_GOTO_PROGRAMS_MM_IO_H
#define CPROVER_GOTO_PROGRAMS_MM_IO_H

class goto_functionst;
class goto_modelt;
class symbol_tablet;

void mm_io(const symbol_tablet &, goto_functionst &);
void mm_io(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_MM_IO_H
