/*******************************************************************\

Module: Utility functions for Kani code contracts.

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_KANI_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_KANI_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_program.h>

#include <goto-instrument/contracts/dynamic-frames/dfcc_loop_contract_mode.h>

#include <map>
#include <set>
#include <unordered_set>

/// Decide if an instruction is call to the kani placeholder
///     kani_loop_invariant(cond);
bool is_kani_loop_invariant(const goto_programt::instructiont instr);

/// Decide if an instruction is call to the kani placeholder
///     kani_loop_invariant_begin();
bool is_kani_loop_invariant_begin(const goto_programt::instructiont instr);

/// Decide if an instruction is call to the kani placeholder
///     kani_loop_invariant_end();
bool is_kani_loop_invariant_end(const goto_programt::instructiont instr);

/// Find loops end with the call to placeholder
///     kani_loop_invariant(cond);
/// and set the spec_loop_invariants sub of the latch node to true
void annotate_kani_loop_invariants(goto_programt &body, messaget &log);

/// Get the instructions `eval_instructions` to evaluate the kani loop
/// invariants. The evaluation result will be `invariant_clause`
void get_kani_invariants(
  const goto_functiont &goto_function,
  const goto_programt::const_targett &loop_head,
  exprt::operandst &invariant_clauses,
  goto_programt::instructionst &eval_instructions);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_UTILS_KANI_H
