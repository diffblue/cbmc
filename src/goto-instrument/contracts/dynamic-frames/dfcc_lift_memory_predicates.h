/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: November 2022

\*******************************************************************/

/// \file
/// Collects all user-defined predicates that call functions
/// is_fresh, pointer_in_range, obeys_contract and lifts them to function taking
/// pointers by reference. When called in assumption contexts,
/// These user-defined predicates update the pointers using side effect in order
/// to make the assumptions described by the predicate hold.
/// In assertion contexts, they behave like the original user-defined predicate
/// i.e. without side effects.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIFT_MEMORY_PREDICATES_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIFT_MEMORY_PREDICATES_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

#include <map>
#include <set>

class dfcc_utilst;
class dfcc_libraryt;
class dfcc_instrumentt;
class message_handlert;
class goto_modelt;
class exprt;
class replace_symbolt;

class dfcc_lift_memory_predicatest
{
public:
  /// \param goto_model The goto model to process
  /// \param utils Utility methods
  /// \param library The contracts instrumentation library
  /// \param instrument The DFCC instrumenter object
  /// \param message_handler Used for messages
  dfcc_lift_memory_predicatest(
    goto_modelt &goto_model,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument,
    message_handlert &message_handler);

  /// \brief Collects and lifts all user-defined memory predicates.
  /// \param[out] discovered_function_pointer_contracts Set of function pointer
  /// contracts discovered during instrumentation
  /// \return The set of predicates that were lifted
  std::set<irep_idt>
  lift_predicates(std::set<irep_idt> &discovered_function_pointer_contracts);

  /// Fixes calls to user-defined memory predicates in the given program,
  /// by adding an address-of to arguments passed in lifted position.
  void fix_calls(goto_programt &program);

  /// Fixes calls to user-defined memory predicates in the given program,
  /// by adding an address-of to arguments passed in lifted position, between
  /// first_instruction (included) and last_instruction (excluded).
  void fix_calls(
    goto_programt &program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction);

protected:
  goto_modelt &goto_model;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  messaget log;
  // index of lifted parameters for lifted functions
  std::map<irep_idt, std::set<std::size_t>> lifted_parameters;

  /// \brief Returns true iff \p goto_program calls core memory predicates.
  /// or one of the functions found in \p predicates .
  bool calls_memory_predicates(
    const goto_programt &goto_program,
    const std::set<irep_idt> &predicates);

  void lift_predicate(
    const irep_idt &function_id,
    std::set<irep_idt> &discovered_function_pointer_contracts);

  void lift_parameters_and_update_body(
    const irep_idt &function_id,
    std::set<irep_idt> &discovered_function_pointer_contracts);

  /// \brief adds a pointer_type to the parameter of a function
  /// \param function_id The function to update
  /// \param parameter_rank The parameter to update
  /// \param replace_lifted_param Symbol replacer (receives `p ~> *p` mappings)
  /// The parameter symbol gets updated in the symbol table and the function
  /// signature gets updated with the new type.
  void add_pointer_type(
    const irep_idt &function_id,
    const std::size_t parameter_rank,
    replace_symbolt &replace_lifted_param);

  /// \brief Computes the subset of function parameters of function_id
  /// that are passed directly to core predicates and must be lifted.
  void collect_parameters_to_lift(const irep_idt &function_id);

  /// \brief True if a function at least had one of its parameters lifted
  bool is_lifted_function(const irep_idt &function_id);
};

#endif
