/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Enum type representing the contract checking and replacement modes.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_MODE_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_MODE_H

/// Enum type representing the contract checking and replacement modes.
enum class dfcc_contract_modet
{
  CHECK,
  REPLACE
};

#endif
