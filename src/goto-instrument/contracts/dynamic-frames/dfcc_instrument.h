/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Add instrumentation to a goto program to perform frame condition checks

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INSTRUMENT_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INSTRUMENT_H

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_program.h>

#include "dfcc_contract_mode.h"

#include <map>
#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;
class cfg_infot;
class dfcc_libraryt;
class dfcc_utilst;

/// This class instruments GOTO functions or instruction sequences
/// for frame condition checking.
class dfcc_instrumentt
{
public:
  dfcc_instrumentt(
    goto_modelt &goto_model,
    messaget &log,
    dfcc_utilst &utils,
    dfcc_libraryt &library);

  /// True if id has `CPROVER_PREFIX` or `__VERIFIER` or `nondet` prefix,
  /// or an `&object`
  bool is_cprover_symbol(const irep_idt &function_id) const;

  /// True iff the symbol an internal symbol
  bool is_internal_symbol(const irep_idt &id) const;

  /// True iff the symbol must not be instrumented because it is an internal
  /// symbol or a CPROVER symbol
  bool do_not_instrument(const irep_idt &id) const;

  /// Instruments a function as a proof harness.
  ///
  /// Instrumenting a harness function just consists in passing a NULL value
  /// for the write_set parameter to all function and function pointer calls
  /// it contains.
  ///
  /// This will result in no write_set updates or checks being performed in
  /// the harness or in the functions called directly from the harness
  /// (and transitively in functions they call).
  ///
  /// One of the functions called directly (or indirectly) by the harness
  /// is eventually going to be a wrapper function that checks the contract
  /// against the function of interest. This wrapper will ignore the NULL
  /// write set it received from the harness and instantiate its own local
  /// write set from the contract and pass it to the function under analysis.
  /// This will trigger cascading checks in all functions called from the
  /// checked function thanks to the propagation of the write set through
  /// function calls and function pointer calls.
  void instrument_harness_function(const irep_idt &function_id);

  /// Instruments a GOTO function by adding an extra write set parameter and
  /// inserting frame condition checks in its goto program.
  void instrument_function(const irep_idt &function_id);

  /// Instruments a GOTO program against a given write set pointer variable.
  void instrument_goto_program(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const exprt &write_set);

  /// Adds the set of instrumented functions to dest
  void get_instrumented_functions(std::set<irep_idt> &dest) const;

protected:
  goto_modelt &goto_model;
  messaget &log;
  message_handlert &message_handler;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  namespacet ns;

  static std::set<irep_idt> function_cache;

  /// Instruments the body of a GOTO function against a given write set.
  void instrument_function_body(
    const irep_idt &function_id,
    const exprt &write_set,
    cfg_infot &cfg_info);

  /// Instruments a sequence of instructions.
  ///
  /// \param function_id name of the enclosing function
  /// (used as prefix for new variables)
  /// \param write_set write set variable to instrument against
  /// \param goto_program goto program to instrument
  /// \param first_instruction first instruction to instrument in the program
  /// \param last_instruction last instruction to instrument (excluded !!!)
  /// \param cfg_info computes local and dirty variables to discard some checks
  /// \param pred filter predicate for instructions
  ///  If `pred` is not provided, all instructions are checked.
  ///  If `pred` is provided, only instructions satisfying pred are checked.
  void instrument_instructions(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt &goto_program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction, // excluding the last
    cfg_infot &cfg_info,
    const std::function<bool(const goto_programt::targett &)> &pred);

  /// When true the symbol `x` in `DECL x` or `DEAD x` must be added explicitly
  /// to the write set. When false, assignments to `x` are implicitly allowed.
  bool must_track_decl_or_dead(
    const goto_programt::targett &target,
    const cfg_infot &cfg_info) const;

  /// Instruments a `DECL x` instruction.
  void instrument_decl(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Instruments a `DEAD x` instruction.
  void instrument_dead(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Returns true iff the lhs of a `ASSIGN lhs := ...` instruction or
  /// `CALL lhs := ...` must be checked against the write set.
  /// When false, the assignment is implicitly allowed.
  bool must_check_lhs(
    const source_locationt &lhs_source_location,
    source_locationt &check_source_location,
    const irep_idt &language_mode,
    const exprt &lhs,
    const cfg_infot &cfg_info);

  void instrument_lhs(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    const exprt &lhs,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Checks if lhs is the `dead_object`, and if the rhs
  /// is an `if_exprt(nondet, ptr, dead_object)` expression.
  /// Returns `ptr` if the pattern was matched, nullptr otherwise.
  const exprt *is_dead_object_update(const exprt &lhs, const exprt &rhs);

  /// Instrument the `lhs` of an `ASSIGN lhs := rhs` instruction by
  /// adding an inclusion check of `lhs` in `write_set`.
  /// If the rhs is an side_effect_expr(ID_allocate)
  void instrument_assign(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Adjusts the arguments of function or function pointer call instruction
  void instrument_call_instruction(
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Same as \ref instrument_call_instruction but inserts a dynamic check
  /// do pass the extra write set parameter only to function pointers that point
  /// to instrumented functions that can effectively accept it.
  void instrument_fptr_call_instruction_dynamic_lookup(
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Inserts deallocation checks and a write set update before a call
  /// to the __CPROVER_deallocate function.
  void instrument_deallocate_call(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Instruments a `CALL lhs := function(params)` instruction by
  /// adding an inclusion check of `lhs` in `write_set`,
  /// and passing `write_set` as an extra argument to the function call.
  void instrument_function_call(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Instruments a `OTHER statement;` instruction.
  /// OTHER instructions can be an  array_set, array_copy, array_replace or
  /// a havoc_object instruction.
  void instrument_other(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);
};

#endif
