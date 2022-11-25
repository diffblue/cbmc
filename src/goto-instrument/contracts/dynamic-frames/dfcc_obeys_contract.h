/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Instruments occurrences of obeys_contract predicates in programs
/// encoding requires and ensures clauses of contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_OBEYS_CONTRACT_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_OBEYS_CONTRACT_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

class goto_modelt;
class message_handlert;
class dfcc_libraryt;
class exprt;

/// Rewrites calls to obeys_contract predicates into calls
/// to the library implementation.
class dfcc_obeys_contractt
{
public:
  /// \param library The contracts instrumentation library
  /// \param message_handler Used for messages
  dfcc_obeys_contractt(
    dfcc_libraryt &library,
    message_handlert &message_handler);

  /// Rewrites calls to obeys_contract predicates into calls
  /// to the library implementation in the given program, passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(
    goto_programt &program,
    const exprt &write_set,
    std::set<irep_idt> &function_pointer_contracts);

  /// Rewrites calls to obeys_contract predicates into calls
  /// to the library implementation in the given program between
  /// first_instruction (included) and last_instruction (excluded), passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(
    goto_programt &program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction,
    const exprt &write_set,
    std::set<irep_idt> &function_pointer_contracts);

protected:
  dfcc_libraryt &library;
  message_handlert &message_handler;
  messaget log;

  /// Extracts the name from the second argument of a call to
  /// `obeys_contract` (modulo any intermediate typecast expressions).
  /// and adds it to function_pointer_contracts
  void get_contract_name(
    const exprt &expr,
    std::set<irep_idt> &function_pointer_contracts);
};

#endif
