/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_loop_contract_mode.h"

#include <util/invariant.h>

dfcc_loop_contract_modet dfcc_loop_contract_mode_from_bools(
  bool apply_loop_contracts,
  bool unwind_transformed_loops)
{
  if(apply_loop_contracts)
  {
    if(unwind_transformed_loops)
    {
      return dfcc_loop_contract_modet::APPLY_UNWIND;
    }
    else
    {
      return dfcc_loop_contract_modet::APPLY;
    }
  }
  else
  {
    return dfcc_loop_contract_modet::NONE;
  }
}

std::string
dfcc_loop_contract_mode_to_string(const dfcc_loop_contract_modet mode)
{
  switch(mode)
  {
  case dfcc_loop_contract_modet::NONE:
    return "dfcc_loop_contract_modet::NONE";
  case dfcc_loop_contract_modet::APPLY:
    return "dfcc_loop_contract_modet::APPLY";
  case dfcc_loop_contract_modet::APPLY_UNWIND:
    return "dfcc_loop_contract_modet::APPLY_UNWIND";
  }
  UNREACHABLE;
}

std::ostream &operator<<(std::ostream &os, const dfcc_loop_contract_modet mode)
{
  os << dfcc_loop_contract_mode_to_string(mode);
  return os;
}
