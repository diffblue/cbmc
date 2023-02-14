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
#include <util/message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_program.h>

#include "dfcc_contract_mode.h"

#include <map>
#include <set>

class goto_modelt;
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
    message_handlert &message_handler,
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
  ///
  /// \param function_id function to instrument
  /// \param function_pointer_contracts contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_harness_function(
    const irep_idt &function_id,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO function by adding an extra write set parameter
  /// and inserting frame condition checks in its GOTO program, as well as
  /// instructions to automatically insert and remove locally declared static
  /// variables in the write set.
  ///
  /// \pre The function must *not* be one of the checked or replaced functions.
  /// For checked/replaced functions \ref instrument_wrapped_function must be
  /// used instead.
  /// \param function_id The name of the function, used to retrieve the function
  /// to instrument and used as prefix when generating new symbols during
  /// instrumentation.
  /// \param function_pointer_contracts contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_function(
    const irep_idt &function_id,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO function by adding an extra write set parameter
  /// and inserting frame condition checks in its GOTO program, as well as
  /// instructions to automatically insert and remove locally declared static
  /// variables in the write set.
  ///
  /// \pre The function must be a function wrapped for contract checking or
  /// replacement. For other functions \ref instrument_function must be used
  /// instead.
  ///
  /// \param wrapped_function_id The name of the function, used to retrieve the
  /// function to instrument and used as prefix when generating new symbols
  /// during instrumentation.
  /// \param initial_function_id The initial name of the function,
  /// before mangling. This is the name used to identify statics symbols in the
  /// symbol table that were locally declared in the function.
  /// \param function_pointer_contracts contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_wrapped_function(
    const irep_idt &wrapped_function_id,
    const irep_idt &initial_function_id,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO program against a given write set variable.
  ///
  /// \remark  Only variables declared within the instruction sequence are
  /// considered local and automatically assignable. In particular, occurrences
  /// of symbols with the `is_parameter` which represent parameters of the
  /// enclosing function are not considered as local to the program.
  /// \remark Local statics declared in the program are *not* searched for and
  /// are *not* added automatically to the write set.
  /// \remark This function is meant to instrument instruction sequences that
  /// were generated from contract clauses.
  ///
  /// \param function_id Name used as prefix when creating new symbols during
  /// instrumentation.
  /// \param goto_program Goto program to instrument.
  /// \param write_set Write set variable to use for instrumentation.
  /// \param function_pointer_contracts Discovered function pointer contracts
  void instrument_goto_program(
    const irep_idt &function_id,
    goto_programt &goto_program,
    const exprt &write_set,
    std::set<irep_idt> &function_pointer_contracts);

  /// Adds the names of instrumented functions to \p dest.
  /// The names are kept track of in the \ref function_cache field.
  void get_instrumented_functions(std::set<irep_idt> &dest) const;

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  namespacet ns;

  /// \brief Keeps track of instrumented functions, so that no function gets
  /// instrumented more than once.
  static std::set<irep_idt> function_cache;

  /// \brief Set of internal symbols which implementation is generated and
  /// inlined into the model at conversion or symex time and must not be
  /// instrumented
  std::set<irep_idt> internal_symbols;

  /// \brief Returns the set of names from the symbol table that
  /// have the static flag set to true and have a source location where the
  /// function field is equal to the given \p function_id .
  /// \param[in] function_id Function name used to collect the statics.
  std::set<symbol_exprt> get_local_statics(const irep_idt &function_id);

  /// \brief Generates a guarded call to record a locally allocated symbol
  /// and inserts it in the goto_program at the target, and moves the target
  /// forward.
  /// ```
  /// IF !write_set GOTO skip_target;
  /// CALL __CPROVER_contracts_write_set_add_allocated(write_set, &x);
  /// skip_target: SKIP;
  /// ```
  /// \param function_id Name of the function in which the instructions is added
  /// \param write_set The write set to the symbol expr to
  /// \param symbol_expr The symbol to add to the write set
  /// \param target The instruction pointer to insert at
  /// \param goto_program the goto_program being instrumented
  void insert_add_allocated_call(
    const irep_idt &function_id,
    const exprt &write_set,
    const symbol_exprt &symbol_expr,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// \brief Generates a guarded call to record the death of a local symbol
  /// and inserts it in the goto_program at the target, and moves the target
  /// forward.
  /// ```c
  /// IF !write_set GOTO skip_target;
  /// CALL __CPROVER_contracts_write_set_record_dead(write_set, &x);
  /// skip_target: SKIP;
  /// ```
  /// \param function_id Name of the function in which the instructions is added
  /// \param write_set The write set to the symbol expr to
  /// \param symbol_expr The symbol to add to the write set
  /// \param target The instruction pointer to insert at
  /// \param goto_program the goto_program being instrumented
  void insert_record_dead_call(
    const irep_idt &function_id,
    const exprt &write_set,
    const symbol_exprt &symbol_expr,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Instruments a GOTO function by adding an extra write set parameter and
  /// inserting frame condition checks in its goto program.
  /// Uses \p function_id_for_local_static_search  to search for local statics
  /// and automatically to add/remove to the write set.
  void instrument_function(
    const irep_idt &function_id,
    const irep_idt &function_id_for_local_static_search,
    std::set<irep_idt> &function_pointer_contracts);

  /// Instruments the body of a GOTO function against a given write set.
  /// Adds the given local statics to the write set in pre and removes them
  /// post.
  void instrument_function_body(
    const irep_idt &function_id,
    const exprt &write_set,
    cfg_infot &cfg_info,
    const std::set<symbol_exprt> &local_statics,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments the instructions found between \p first_instruction and
  /// \p last_instruction in the instructions of \p goto_program against the
  /// given \p write_set variable.
  ///
  /// \param function_id Name of the enclosing function used as prefix for new
  /// variables generated during instrumentation.
  /// \param write_set Write set variable to instrument against
  /// \param goto_program Program to instrument the instructions of
  /// \param first_instruction First instruction to instrument in the program
  /// \param last_instruction Last instruction to instrument (excluded !!!)
  /// \param cfg_info Computes local and dirty variables to discard some checks
  /// \param pred filter predicate for instructions. If \p pred is not provided,
  /// all instructions are instrumented. If \p pred is provided, only
  /// instructions satisfying \p pred are instrumented.
  /// \param function_pointer_contracts contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_instructions(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt &goto_program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction, // excluding the last
    cfg_infot &cfg_info,
    const std::function<bool(const goto_programt::targett &)> &pred,
    std::set<irep_idt> &function_pointer_contracts);

  /// Returns `true` if the symbol `x` in `DECL x` or `DEAD x` must be added
  /// explicitly to the write set. Returns `false` when assignments to `x` must
  /// be implicitly allowed.
  bool must_track_decl_or_dead(
    const goto_programt::targett &target,
    const cfg_infot &cfg_info) const;

  /// Instruments a `DECL x` instruction.
  /// \pre \p target points to a `DECL` instruction
  void instrument_decl(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Instruments a `DEAD x` instruction.
  /// \pre \p target points to a `DEAD` instruction
  void instrument_dead(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Returns true iff the lhs of a `ASSIGN lhs := ...` instruction or
  /// `CALL lhs := ...` must be checked against the write set.
  /// Returns false if the assignment must be implicitly allowed.
  /// Works in tandem with \ref must_track_decl_or_dead
  bool must_check_lhs(
    const source_locationt &lhs_source_location,
    source_locationt &check_source_location,
    const irep_idt &language_mode,
    const exprt &lhs,
    const cfg_infot &cfg_info);

  /// \brief Instruments the LHS of an assignment instruction instruction by
  /// adding an inclusion check of \p lhs in \p write_set.
  void instrument_lhs(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    const exprt &lhs,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Checks if \p lhs is the `dead_object`, and if \p rhs
  /// is an `if_exprt(nondet, ptr, dead_object)` expression.
  /// Returns a pointer to the `ptr` expression if the pattern was matched,
  /// returns `nullptr` otherwise.
  optionalt<exprt> is_dead_object_update(const exprt &lhs, const exprt &rhs);

  /// Instrument the \p lhs of an `ASSIGN lhs := rhs` instruction by
  /// adding an inclusion check of \p lhs in \p write_set.
  /// If \ref is_dead_object_update returns a successful match, the matched
  /// pointer expression is removed from \p write_set.
  /// If \p rhs is a `side_effect_expr(ID_allocate)`, the allocated pointer gets
  /// added to the \p write_set.
  /// \pre \p target points to an `ASSIGN` instruction.
  void instrument_assign(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Adds the \p write_set as extra argument to a function of function pointer
  /// call instruction.
  /// \pre \p target points to a `CALL` instruction.
  void instrument_call_instruction(
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Before calling a function pointer, performs a dynamic lookup into
  /// the map of instrumented function provided by
  /// \ref dfcc_libraryt.get_instrumented_functions_map_symbol,
  /// and passes the write_set parameter to the function pointer only if
  /// it points to a function known to be instrumented and hence able to accept
  /// this parameter.
  /// \pre \p target points to a `CALL` instruction where the function
  /// expression is not a \ref symbol_exprt.
  void instrument_fptr_call_instruction_dynamic_lookup(
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Inserts deallocation checks and a write set update before a call
  /// to the __CPROVER_deallocate function.
  /// \pre \p target points to a `CALL __CPROVER_deallocate` instruction.
  void instrument_deallocate_call(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program);

  /// Instruments a `CALL lhs := function(params)` instruction by
  /// adding an inclusion check of `lhs` in `write_set`,
  /// and passing `write_set` as an extra argument to the function call.
  /// \pre \p target points to a `CALL` instruction.
  void instrument_function_call(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);

  /// Instruments a `OTHER statement;` instruction.
  /// OTHER instructions can be an  array_set, array_copy, array_replace or
  /// a havoc_object instruction.
  /// \pre \p target points to an `OTHER` instruction.
  void instrument_other(
    const irep_idt &function_id,
    const exprt &write_set,
    goto_programt::targett &target,
    goto_programt &goto_program,
    cfg_infot &cfg_info);
};

#endif
