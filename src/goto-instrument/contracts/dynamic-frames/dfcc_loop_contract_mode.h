/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Enumeration representing the instrumentation mode for loop contracts.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_CONTRACT_MODE_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_CONTRACT_MODE_H

#include <string>

/// Enumeration representing the instrumentation mode for loop contracts.
enum class dfcc_loop_contract_modet
{
  /// Do not apply loop contracts
  NONE,
  /// Apply loop contracts
  APPLY,
  /// Apply loop contracts and unwind the resulting base + step encoding
  APPLY_UNWIND
};

/// Generates an enum value from boolean flags for application and unwinding.
dfcc_loop_contract_modet dfcc_loop_contract_mode_from_bools(
  bool apply_loop_contracts,
  bool unwind_transformed_loops);

std::string dfcc_loop_contract_mode_to_string(dfcc_loop_contract_modet mode);

std::ostream &operator<<(std::ostream &os, const dfcc_loop_contract_modet mode);

#endif
