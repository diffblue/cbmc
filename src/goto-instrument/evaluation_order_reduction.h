/*******************************************************************\

Module: Partial-order reduction for --evaluation-order-check

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Partial-order reduction for --evaluation-order-check
///
/// With --evaluation-order-check, goto conversion executes the side effects
/// (events) of a full expression in all orders that the C standard permits,
/// emitting each event once for each round in which it may execute (see
/// goto_convert_evaluation_order.cpp). An event that is unordered with some
/// other event additionally gets a *pinned* copy, which executes before all
/// other events and is disabled by default.
///
/// An event e commutes with all events it is unordered with when, taking
/// the functions it calls into account, it neither writes memory that such
/// an event reads or writes, nor reads memory that such an event writes;
/// when e moreover does not write memory that a checked read in its window
/// reads, executing e at any admissible point yields the same result. If
/// this holds for e and all events within its operands, this pass enables
/// e's pinned copy and disables its other copies, which symex then skips.
///
/// Footprints are computed per memory object (field- and array-insensitive)
/// using a flow-insensitive value-set analysis, which also accounts for
/// values assigned by events that execute before the event. Accesses whose
/// target is unknown, and instructions whose effects are not modelled here
/// (such as array_set or thread creation), make an event conflict with all
/// others. Direct accesses to the parameters and local variables of called
/// functions are ignored, as each call has its own instance of them.
///
/// Limitations of this first version:
/// - Allocation (malloc) updates bookkeeping variables of the CPROVER
///   library, so two events that allocate memory do not commute.
/// - A pinned event keeps its (now virtual) round, which only matters for the
///   checks of reads. The remaining events thus still choose among all n
///   rounds, rather than among n minus the number of pinned events.
/// - Only cbmc applies the reduction; other tools leave the flags unset,
///   which is sound but explores all orders.
///
/// The pass was validated by comparing all property results against the
/// unreduced encoding on the regression tests (with --evaluation-order-check
/// added to all of them) and on 2000 randomly generated programs that mix
/// calls, increments, divisions, and writes through pointers that other
/// calls redirect.

#ifndef CPROVER_GOTO_INSTRUMENT_EVALUATION_ORDER_REDUCTION_H
#define CPROVER_GOTO_INSTRUMENT_EVALUATION_ORDER_REDUCTION_H

class goto_modelt;
class message_handlert;

/// Enable the pinned copies of all events in \p goto_model that commute with
/// all events they are unordered with, see the file description. Call this
/// once the program is complete (all functions linked, function pointers
/// removed); events whose footprint involves functions without a body are
/// treated as if those functions had no side effects, as symex does.
void reduce_evaluation_order(goto_modelt &goto_model, message_handlert &);

#endif // CPROVER_GOTO_INSTRUMENT_EVALUATION_ORDER_REDUCTION_H
