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
#include "dfcc_instrument_loop.h"
#include "dfcc_loop_contract_mode.h"

#include <map>
#include <set>

class goto_modelt;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;
class dfcc_libraryt;
class dfcc_spec_functionst;
class dfcc_contract_clauses_codegent;
class dfcc_utilst;
class dfcc_loop_utilst;
class dirtyt;
class dfcc_cfg_infot;

/// This class instruments GOTO functions or instruction sequences
/// for frame condition checking and loop contracts.
class dfcc_instrumentt
{
public:
  dfcc_instrumentt(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_spec_functionst &spec_functions,
    dfcc_contract_clauses_codegent &contract_clauses_codegen);

  /// True iff the symbol an internal symbol
  bool is_internal_symbol(const irep_idt &id) const;

  /// True iff the symbol must not be instrumented because it is an internal
  /// symbol or a CPROVER symbol
  bool do_not_instrument(const irep_idt &id) const;

  /// Instruments a GOTO function used as a proof harness. Proof harnesses
  /// are closed functions without parameters, so we declare a local write set
  /// pointer and initialise it to NULL, and check body instructions against
  /// that NULL write set.
  ///
  /// By using a NULL write set pointer we ensure that no checks are being
  /// performed in the harness or in the functions called from the harness,
  /// except in the following cases:
  /// 1. One of the functions called directly (or indirectly) by the harness
  /// is a verification wrapper function that checks some contract against some
  /// function. This wrapper will ignore the NULL write set it received from the
  /// harness and will instantiate its own write set from the contract and pass
  /// it to the function under analysis.
  /// 2. The harness function contains loops that have contracts.
  /// A write set is created for each loop and loop instructions instrumented
  /// against that write set. The write set is propagated to all functions
  /// called from the loop.
  ///
  /// \param function_id Function to instrument
  /// \param loop_contract_mode Mode to use for loop contracts
  /// \param function_pointer_contracts Contract names discovered in calls to
  /// the `obeys_contract` predicate are added to this set.
  void instrument_harness_function(
    const irep_idt &function_id,
    const dfcc_loop_contract_modet loop_contract_mode,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO function by adding an extra write set parameter
  /// and instrumenting its body instructions against the write set. Adds ghost
  /// instructions that automatically insert locally declared static variables
  /// to the write set when entering the function and removing them upon exit.
  ///
  /// \pre The function must *not* be one of the functions checked against a
  /// contract or replaced by a contract. The method
  /// \ref instrument_wrapped_function must be used to instrument check/replaced
  /// functions instead.
  ///
  /// \param function_id The name of the function, used to retrieve the function
  /// to instrument and used as prefix when generating new symbols during
  /// instrumentation.
  /// \param loop_contract_mode Mode to use for loop contracts
  /// \param function_pointer_contracts Contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_function(
    const irep_idt &function_id,
    const dfcc_loop_contract_modet loop_contract_mode,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO function by adding an extra write set parameter
  /// and inserting frame condition checks in its GOTO program, as well as
  /// instructions to automatically insert and remove locally declared static
  /// variables in the write set.
  ///
  /// \pre The function must be a function wrapped for contract checking or
  /// replacement checking. For other functions \ref instrument_function must
  /// be used instead. The difference is that checked or replaced functions have
  /// their name mangled, so the the search for local statics uses a possibly
  /// different function identifier as base name for static symbols.
  ///
  /// \param wrapped_function_id The name of the function, used to retrieve the
  /// function to instrument and used as prefix when generating new symbols
  /// during instrumentation.
  /// \param initial_function_id The initial name of the function,
  /// before mangling. This is the name used to identify statics symbols in the
  /// symbol table that were locally declared in the function.
  /// \param loop_contract_mode Mode to use for loop contracts
  /// \param function_pointer_contracts contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_wrapped_function(
    const irep_idt &wrapped_function_id,
    const irep_idt &initial_function_id,
    const dfcc_loop_contract_modet loop_contract_mode,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments a GOTO program against a given write set variable.
  ///
  /// \remark This function is meant to instrument instruction
  /// sequences generated from contract clauses.
  /// \remark Only variables declared within the instruction sequence are
  /// considered local and implicitly assignable. In particular, occurrences
  /// of symbols with the `is_parameter` flag set to true, which represent
  /// parameters of the enclosing function, are not considered implicitly
  /// assignable.
  /// \remark Loop contracts are never applied.
  /// \remark Local statics are *not* collected and added to the write set.
  ///
  /// \param function_id Name used as prefix when creating new symbols during
  /// instrumentation.
  /// \param goto_program GOTO program to instrument.
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

  /// \return The maximum assigns clause size discovered when instrumenting
  /// loop contracts
  std::size_t get_max_assigns_clause_size() const;

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_spec_functionst &spec_functions;
  dfcc_contract_clauses_codegent &contract_clauses_codegen;
  dfcc_instrument_loopt instrument_loop;
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
  /// CALL __CPROVER_contracts_write_set_add_decl(write_set, &x);
  /// skip_target: SKIP;
  /// ```
  /// \param function_id Name of the function in which the instructions is added
  /// \param write_set The write set to the symbol expr to
  /// \param symbol_expr The symbol to add to the write set
  /// \param target The instruction pointer to insert at
  /// \param goto_program the goto_program being instrumented
  void insert_add_decl_call(
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

  /// Instruments the body of a GOTO function against a given write set.
  /// Adds the given local statics to the write set in pre and removes them
  /// post.
  void instrument_goto_function(
    const irep_idt &function_id,
    goto_functiont &goto_function,
    const exprt &write_set,
    const std::set<symbol_exprt> &local_statics,
    const dfcc_loop_contract_modet loop_contract_mode,
    std::set<irep_idt> &function_pointer_contracts);

  /// \brief Instruments the instructions found between \p first_instruction and
  /// \p last_instruction in the instructions of \p goto_program against the
  /// given \p write_set variable.
  ///
  /// \param function_id Name of the enclosing function used as prefix for new
  /// variables generated during instrumentation.
  /// \param goto_program Program to instrument the instructions of
  /// \param first_instruction First instruction to instrument in the program
  /// \param last_instruction Last instruction to instrument (excluded !!!)
  /// \param cfg_info Computes local and dirty variables to discard some checks
  /// \param function_pointer_contracts Contracts discovered in calls to
  /// the obeys_contract predicate are added to this set.
  void instrument_instructions(
    const irep_idt &function_id,
    goto_programt &goto_program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction, // excluding the last
    dfcc_cfg_infot &cfg_info,
    std::set<irep_idt> &function_pointer_contracts);

  /// Instruments a `DECL x` instruction.
  /// \pre \p target points to a `DECL` instruction
  void instrument_decl(
    const irep_idt &function_id,
    goto_programt::targett &target,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

  /// Instruments a `DEAD x` instruction.
  /// \pre \p target points to a `DEAD` instruction
  void instrument_dead(
    const irep_idt &function_id,
    goto_programt::targett &target,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

  /// \brief Instruments the LHS of an assignment instruction instruction by
  /// adding an inclusion check of \p lhs in \p write_set.
  void instrument_lhs(
    const irep_idt &function_id,
    goto_programt::targett &target,
    const exprt &lhs,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

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
    goto_programt::targett &target,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

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
    goto_programt::targett &target,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

  /// Instruments a `OTHER statement;` instruction.
  /// OTHER instructions can be an  array_set, array_copy, array_replace or
  /// a havoc_object instruction.
  /// \pre \p target points to an `OTHER` instruction.
  void instrument_other(
    const irep_idt &function_id,
    goto_programt::targett &target,
    goto_programt &goto_program,
    dfcc_cfg_infot &cfg_info);

  /// \brief Applies loop contracts transformations to the given GOTO function,
  /// using the given cfg_info instance to drive the transformation.
  ///
  /// \pre Instructions of the function must already have been instrumented for
  /// DFCC using the same cfg_info.
  void apply_loop_contracts(
    const irep_idt &function_id,
    goto_functiont &goto_function,
    dfcc_cfg_infot &cfg_info,
    const dfcc_loop_contract_modet loop_contract_mode,
    const std::set<symbol_exprt> &local_statics,
    std::set<irep_idt> &function_pointer_contracts);
};

#endif
