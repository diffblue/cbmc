/*******************************************************************\

Module: Dynamic frame condition checking for loop contracts

Author: Qinheping Hu, qinhh@amazon.com

Author: Remi Delmas, delmasrd@amazon.com

Date: April 2023

\*******************************************************************/

/// \file
/// This class applies the loop contract transformation to a loop in a goto
/// function.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INSTRUMENT_LOOP_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INSTRUMENT_LOOP_H

#include <util/message.h>

#include <goto-programs/goto_model.h>

#include <analyses/local_may_alias.h>

class dfcc_spec_functionst;
class dfcc_utilst;
class dfcc_libraryt;
class dfcc_instrumentt;
class dfcc_spec_functionst;
class dfcc_contract_clauses_codegent;
class dfcc_cfg_infot;

/// This class applies the loop contract transformation to a loop in a goto
/// function.
class dfcc_instrument_loopt
{
public:
  /// \brief Constructor for the loop contract instrumentation class.
  /// \param[inout] goto_model GOTO model being instrumented
  /// \param[inout] message_handler For status/debug output
  /// \param[inout] utils DFCC utility methods
  /// \param[inout] library DFCC instrumentation library functions
  /// \param[inout] spec_functions Class used to translate assigns clauses
  /// to GOTO instructions.
  /// \param[inout] contract_clauses_codegen Class used to generate GOTO
  /// instructions from contract clauses.
  dfcc_instrument_loopt(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_spec_functionst &spec_functions,
    dfcc_contract_clauses_codegent &contract_clauses_codegen);

  /// \brief Replaces a loop by a base + step abstraction generated from its
  /// contract.
  /// \param[in] loop_id Id of the loop to transform in `cfg_info`.
  /// \param[in] function_id Id of the function in which that loop is.
  /// \param[inout] goto_function GOTO function to transform.
  /// \param[inout] cfg_info Control flow graph information for `goto_function`.
  /// \param[in] local_statics Set of local statics declared in `goto_function`.
  /// \param[out] function_pointer_contracts Destination set for function
  /// pointer contracts discovered during the loop contract transformation.
  ///
  /// \details The loop:
  ///
  /// ```
  ///   ... preamble ...
  /// HEAD:
  ///   ... eval guard ...
  ///   if (!guard)
  ///     goto EXIT;
  ///   ... loop body ...
  ///   goto HEAD;
  /// EXIT:
  ///   ... postamble ...
  /// ```
  ///
  /// Gets rewritten into:
  ///
  /// ```
  ///   ... preamble ...
  ///
  ///   // Prehead block: Declare & initialize instrumentation variables
  ///   snapshot loop_entry history vars;
  ///   entered_loop = false
  ///   initial_invariant = loop_invariant;
  ///   in_base_case = true;
  ///   __ws_loop;
  ///   ws_loop := address_of(__ws_loop);
  ///   __write_set_create(ws_loop);
  ///   __write_set_add(ws_loop, loop_assigns);
  ///   __write_set_add(ws_loop, local_statics);
  ///   GOTO HEAD;
  ///
  /// STEP: // Loop step block: havoc the loop state
  ///   ASSERT(initial_invariant);
  ///   __write_set_check_inclusion(ws_loop, ws_parent);
  ///   in_base_case = false;
  ///   in_loop_havoc_block = true;
  ///   havoc(assigns_clause_targets);
  ///   in_loop_havoc_block = false;
  ///   ASSUME(loop_invariant);
  ///   old_variant = loop_decreases;
  ///
  /// HEAD: // Loop body block
  ///   ... eval guard ...
  ///   IF (!guard) GOTO EXIT;
  ///   ... loop body ...
  ///   // instrumentation
  ///   entered_loop = true
  ///   // Jump back to the step case if the loop can run at least once
  ///   IF (in_base_case) GOTO STEP;
  ///   ASSERT(loop_invariant);
  //    new_variant = loop_decreases;
  ///   ASSERT(new_variant < old_variant);
  ///   ASSUME(false);
  ///
  /// EXIT:
  ///   // check that step case was checked if loop can run once
  ///   ASSUME (entered_loop ==> !in_base_case);
  ///   DEAD loop_entry history vars, in_base_case;
  ///   DEAD initial_invariant, entered_loop;
  ///   DEAD old_variant, in_loop_havoc_block;
  ///   __write_set_release(w_loop);
  ///   DEAD __ws_loop, ws_loop;
  ///
  ///   ... postamble ...
  /// ```
  ///
  /// Where the EXIT block is inserted at the target instruction of each exiting
  /// instruction.
  ///
  void operator()(
    const std::size_t loop_id,
    const irep_idt &function_id,
    goto_functiont &goto_function,
    dfcc_cfg_infot &cfg_info,
    const std::set<symbol_exprt> &local_statics,
    std::set<irep_idt> &function_pointer_contracts);

  /// Maximum number of assigns clause targets
  std::size_t get_max_assigns_clause_size() const
  {
    return max_assigns_clause_size;
  }

protected:
  // keeps track of the maximum number of assigns clause targets
  std::size_t max_assigns_clause_size = 0;
  goto_modelt &goto_model;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_spec_functionst &spec_functions;
  dfcc_contract_clauses_codegent &contract_clauses_codegen;
  namespacet ns;

  /// \brief Adds instructions of prehead block, and return history variables.
  ///
  /// \details Occurrences of history expressions in invariant expressions are
  /// replaced by fresh variables and instructions to snapshot their value
  /// before entering the loop are added to the pre-head instructions.
  /// The mapping of history variables to fresh variables is returned by the
  /// function.
  ///
  /// ```
  ///   ... preamble ...
  ///
  ///   // Prehead block: Declare & initialize instrumentation variables
  ///   snapshot loop_entry history vars;
  ///   entered_loop = false
  ///   initial_invariant = loop_invariant;
  ///   in_base_case = true;
  ///   __ws_loop;
  ///   ws_loop := address_of(__ws_loop);
  ///   ws_loop := __write_set_create();
  ///   __write_set_add(ws_loop, loop_assigns);
  ///   __write_set_add(ws_loop, local_statics);
  ///   GOTO HEAD;
  /// ```
  ///
  /// \param[in] loop_id Id of the loop to transform.
  /// \param[inout] goto_function The function containing the loop.
  /// \param[inout] symbol_table Symbol table of the model.
  /// \param[inout] loop_head Head node of the loop.
  /// \param[inout] loop_latch Latch node of the loop.
  /// \param[out] assigns_instrs `goto_programt` that contains instructions of
  ///                       populating assigns into the loop write set.
  /// \param[out] invariant Loop invariants.
  /// \param[in] assigns Assigns targets of the loop.
  /// \param[in] loop_write_set Stack allocated loop write set variable.
  /// \param[in] addr_of_loop_write_set Loop write set pointer variable.
  /// \param[in] entered_loop temporary variable `entered_loop`.
  /// \param[in] initial_invariant temporary variable `initial_invariant`.
  /// \param[in] in_base_case temporary variable `in_base_case`.
  /// \param[in] symbol_mode Language mode of the function.
  /// \return `history_var_map` that maps variables to loop_entry variables.
  std::map<exprt, exprt> add_prehead_instructions(
    const std::size_t loop_id,
    goto_functionst::goto_functiont &goto_function,
    symbol_tablet &symbol_table,
    goto_programt::targett loop_head,
    goto_programt::targett loop_latch,
    goto_programt &assigns_instrs,
    exprt &invariant,
    const exprt::operandst &assigns,
    const symbol_exprt &loop_write_set,
    const symbol_exprt &addr_of_loop_write_set,
    const symbol_exprt &entered_loop,
    const symbol_exprt &initial_invariant,
    const symbol_exprt &in_base_case,
    const irep_idt &symbol_mode);

  /// \brief Adds instructions of the step block, and returns the STEP
  /// jump target so that it can be used to jump back from the loop body block.
  ///
  /// ```
  /// STEP: // Loop step block: havoc the loop state
  ///   ASSERT(initial_invariant);
  ///   __write_set_check_inclusion(ws_loop, ws_parent);
  ///   in_base_case = false;
  ///   in_loop_havoc_block = true;
  ///   havoc(assigns_clause_targets);
  ///   in_loop_havoc_block = false;
  ///   ASSUME(loop_invariant);
  ///   old_variant = loop_decreases;
  /// ```
  ///
  /// \param[in] loop_id Id of the loop to transform.
  /// \param[in] cbmc_loop_id Id assigned to the loop by CBMC's loop numbering.
  /// \param[in] function_id Id of the function.
  /// \param[inout] goto_function The function containing the loop.
  /// \param[inout] symbol_table Symbol table of the model.
  /// \param[in] loop_head Head node of the loop.
  /// \param[in] loop_latch Latch node of the loop.
  /// \param[inout] havoc_instrs `goto_programt` that contains instructions of
  ///                     havocing assigns targets in the write set.
  /// \param[in] invariant Loop invariant.
  /// \param[in] decreases_clauses Decreases clause.
  /// \param[in] loop_write_set Stack allocated loop write set variable.
  /// \param[in] outer_write_set The write set of the outer loop.
  /// \param[in] initial_invariant temporary variable `initial_invariant`.
  /// \param[in] in_base_case temporary variable `in_base_case`.
  /// \param[in] old_decreases_vars temporary vars of decreases clauses.
  /// \param[in] symbol_mode Language mode of the function.
  /// \return The STEP jump target.
  goto_programt::instructiont::targett add_step_instructions(
    const std::size_t loop_id,
    const std::size_t cbmc_loop_id,
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function,
    symbol_tablet &symbol_table,
    goto_programt::targett loop_head,
    goto_programt::targett loop_latch,
    goto_programt &havoc_instrs,
    const exprt &invariant,
    const exprt::operandst &decreases_clauses,
    const symbol_exprt &loop_write_set,
    const exprt &outer_write_set,
    const symbol_exprt &initial_invariant,
    const symbol_exprt &in_base_case,
    const std::vector<symbol_exprt> &old_decreases_vars,
    const irep_idt &symbol_mode);

  /// \brief Adds instructions of the body block.
  ///
  /// ```
  /// HEAD: // Loop body block
  ///   ... eval guard ...
  ///   IF (!guard) GOTO EXIT;
  ///   ... loop body ...
  ///   // instrumentation
  ///   entered_loop = true
  ///   // Jump back to the step case if the loop can run at least once
  ///   IF (in_base_case) GOTO STEP;
  ///   ASSERT(loop_invariant);
  ///    new_variant = loop_decreases;
  ///   ASSERT(new_variant < old_variant);
  ///   ASSUME(false);
  /// ```
  ///
  /// \param[in] loop_id Id assigned to the loop by the `cfg_info` numbering.
  /// \param[in] cbmc_loop_id Id assigned to the loop by CBMC's numbering.
  /// \param[inout] goto_function The function containing the loop.
  /// \param[inout] symbol_table Symbol table of the model.
  /// \param[in] loop_head Head node of the loop.
  /// \param[in] loop_latch Latch node of the loop.
  /// \param[in] invariant Loop invariant.
  /// \param[in] decreases_clauses Decreases clause.
  /// \param[in] entered_loop temporary variable `entered_loop`.
  /// \param[in] in_base_case temporary variable `in_base_case`.
  /// \param[in] old_decreases_vars temporary vars of old decreases clauses.
  /// \param[in] new_decreases_vars temporary vars of new decreases clauses.
  /// \param[in] step_case_target Target of the head of the step case block.
  /// \param[in] symbol_mode Language mode of the function.
  void add_body_instructions(
    const std::size_t loop_id,
    const std::size_t cbmc_loop_id,
    goto_functionst::goto_functiont &goto_function,
    symbol_tablet &symbol_table,
    goto_programt::targett loop_head,
    goto_programt::targett loop_latch,
    const exprt &invariant,
    const exprt::operandst &decreases_clauses,
    const symbol_exprt &entered_loop,
    const symbol_exprt &in_base_case,
    const std::vector<symbol_exprt> &old_decreases_vars,
    const std::vector<symbol_exprt> &new_decreases_vars,
    const goto_programt::instructiont::targett &step_case_target,
    const irep_idt &symbol_mode);

  /// \brief Adds instructions of the exit block.
  ///
  /// ```
  /// EXIT:
  ///   // check that step case was checked if loop can run once
  ///   ASSUME (entered_loop ==> !in_base_case);
  ///   DEAD loop_entry history vars, in_base_case;
  ///   DEAD initial_invariant, entered_loop;
  ///   DEAD old_variant, in_loop_havoc_block;
  ///   __write_set_release(w_loop);
  ///   DEAD __ws_loop, ws_loop;
  ///
  ///   ... postamble ...
  /// ```
  ///
  /// An EXIT block is inserted at the target instruction of each exiting
  /// instruction.
  ///
  /// \param[in] loop_id Id assigned to the loop by the `cfg_info` numbering.
  /// \param[in] cbmc_loop_id Id assigned to the loop by CBMC's loop numbering.
  /// \param[inout] goto_function The function containing the loop.
  /// \param[in] loop_head Head node of the loop.
  /// \param[in] loop_write_set Stack allocated loop write set variable.
  /// \param[in] addr_of_loop_write_set Loop write set pointer variable.
  /// \param[in] history_var_map Map storing history variables of the loop.
  /// \param[in] entered_loop temporary variable `entered_loop`.
  /// \param[in] initial_invariant temporary variable `initial_invariant`.
  /// \param[in] in_base_case temporary variable `in_base_case`.
  /// \param[in] old_decreases_vars temporary vars of old decreases clauses.
  /// \param[in] new_decreases_vars temporary vars of new decreases clauses.
  void add_exit_instructions(
    const std::size_t loop_id,
    const std::size_t cbmc_loop_id,
    goto_functionst::goto_functiont &goto_function,
    goto_programt::targett loop_head,
    const symbol_exprt &loop_write_set,
    const symbol_exprt &addr_of_loop_write_set,
    const std::map<exprt, exprt> &history_var_map,
    const symbol_exprt &entered_loop,
    const symbol_exprt &initial_invariant,
    const symbol_exprt &in_base_case,
    const std::vector<symbol_exprt> &old_decreases_vars,
    const std::vector<symbol_exprt> &new_decreases_vars);
};

#endif
