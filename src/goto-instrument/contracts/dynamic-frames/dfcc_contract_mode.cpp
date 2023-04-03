/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_contract_mode.h"

#include <util/invariant.h>

std::string dfcc_contract_mode_to_string(const dfcc_contract_modet mode)
{
  switch(mode)
  {
  case dfcc_contract_modet::CHECK:
    return "dfcc_contract_modet::CHECK";
  case dfcc_contract_modet::REPLACE:
    return "dfcc_contract_modet::REPLACE";
  }
  UNREACHABLE;
}

std::ostream &operator<<(std::ostream &os, const dfcc_contract_modet mode)
{
  os << dfcc_contract_mode_to_string(mode);
  return os;
}
