/*******************************************************************\

Module: Race Detection for Threaded Goto Programs

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

/// \file
/// Race Detection for Threaded Goto Programs
///
/// This implements a data-race detector for concurrent programs, inspired by
/// the Eraser algorithm (Savage et al., "Eraser: A Dynamic Data Race Detector
/// for Multithreaded Programs", ACM TOCS 1997). While Eraser uses lockset
/// tracking at runtime, this implementation adapts the core idea for static
/// verification via bounded model checking: it instruments the program with
/// boolean "write guard" flags and assertions so that CBMC's exploration of
/// thread interleavings can reveal conflicting concurrent accesses.
///
/// A data race occurs when two threads access the same shared memory location
/// concurrently and at least one access is a write. This instrumentation
/// detects two kinds of races:
/// - R/W races: one thread reads a variable while another writes it.
/// - W/W races: two threads write the same variable concurrently.
///
/// For each assignment or function call that accesses shared variables, the
/// instrumentation replaces the original instruction with the following
/// sequence:
///
/// 1. For each shared variable `x` written: set `x$w_guard` to the guard
///    condition under which the write occurs.
/// 2. Execute the original instruction.
/// 3. For each shared variable `x` written: reset `x$w_guard` to false.
/// 4. For each shared variable `y` read: assert `!y$w_guard` (R/W check).
/// 5. For each shared variable `x` written: assert `!x$w_guard` (W/W check).
///
/// For instructions that only read shared variables (GOTO/ASSUME/ASSERT
/// guards, SET_RETURN_VALUE), only R/W assertions (step 4) are added before
/// the instruction.
///
/// During symbolic execution of concurrent programs, CBMC explores thread
/// interleavings. If another thread's write guard is set (step 1) when the
/// current thread checks it (steps 4/5), the assertion fails, indicating a
/// data race.
///
/// Pointer dereferences are resolved using value-set analysis (or, when
/// LOCAL_MAY is defined, local may-alias analysis) so that races through
/// aliased pointer accesses are detected. For example, if thread A writes
/// `*p` and thread B writes `x`, and `p` points to `x`, the instrumentation
/// will detect the W/W race on `x`.

#ifndef CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
#define CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H

#ifdef LOCAL_MAY
#  include <goto-programs/goto_functions.h>
#endif

#include <util/irep.h>

class goto_modelt;
class goto_programt;
class message_handlert;
class value_setst;

/// Instrument a single function with data-race detection assertions.
/// \param value_sets: value-set analysis results for pointer resolution
/// \param symbol_table: the symbol table (modified to add guard symbols)
/// \param function_id: identifier of the function being instrumented
/// \param goto_program: the function body to instrument
/// \param message_handler: handler for status and diagnostic messages
void race_check(
  value_setst &,
  class symbol_table_baset &,
  const irep_idt &function_id,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program,
  message_handlert &);

/// Instrument all functions in a goto model with data-race detection
/// assertions. Skips the entry point and the initialization function.
/// \param value_sets: value-set analysis results for pointer resolution
/// \param goto_model: the goto model to instrument
/// \param message_handler: handler for status and diagnostic messages
void race_check(value_setst &, goto_modelt &, message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_RACE_CHECK_H
