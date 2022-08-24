/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Abstract interface to generate contract checking and contract
/// replacement instructions from contracts.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_HANDLER_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_HANDLER_H

#include "dfcc_contract_mode.h"

#include <set>

class goto_programt;
class symbolt;

/// An abstract interface offering functions to generate GOTO instructions
/// encoding a contract in CHECK or REPLACE mode.
class dfcc_contract_handlert
{
public:
  /// Adds instruction modeling the contract to the `dest` program.
  ///
  /// \param[in] translation_mode CHECK or REPLACE mode
  /// \param[in] wrapped_id name of function that is being checked/replaced
  /// \param[in] wrapper_id name of function receiving the instructions
  /// \param[in] contract_id name of the contract to check
  /// \param[in] caller_write_set_symbol extra parameter of the wrapper
  /// function through which the caller's write set is passed
  /// \param[out] dest program where instructions are added
  /// (should eventually become the body of wrapper_id)
  /// \param[out] function_pointer_contracts list of contracts found in either
  /// function pointer requires or ensures clauses. These contracts need to
  /// be swapped and wrapped with themselves in replacement mode
  /// if they are not already.
  ///
  /// In CHECK mode, the caller_write_set is ignored and the generated
  /// instructions are:
  /// - assume requires clauses
  /// - assume requires clauses about function pointers contracts
  /// - capture history variables for the ensures clauses
  /// - create and populate write set from the contract
  /// - call the checked function with the contract's write set
  /// - assert ensures clauses
  /// - assert ensures clauses about function pointers contracts
  ///
  /// In REPLACE mode, the generated instructions are:
  /// - assert requires clauses
  /// - assert requires clauses about function pointers contracts
  /// - capture history variables for ensures clauses
  /// - create write set from the contract
  /// - check write set inclusion in the caller's write set
  /// - havoc assigns clause targets set and call return value to nondet
  /// - nondeterminstically free freeable targets specified by the frees clause
  /// - assume ensures clauses
  /// - assume ensures clauses about function pointers contracts
  virtual void add_contract_instructions(
    const dfcc_contract_modet contract_mode,
    const irep_idt &wrapper_id,
    const irep_idt &wrapped_id,
    const irep_idt &contract_id,
    const symbolt &caller_write_set_symbol,
    goto_programt &dest,
    std::set<irep_idt> &function_pointer_contracts) = 0;

  /// Returns the size of the assigns clause of the given contract_id
  /// in number of targets.
  virtual const int get_assigns_clause_size(const irep_idt &contract_id) = 0;
};

#endif
