/*******************************************************************\

Module: Config for loop contract

Author: Qinheping Hu

Date: June 2024

\*******************************************************************/

/// \file
/// Config for loop contract

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_LOOP_CONTRACT_CONFIG_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_LOOP_CONTRACT_CONFIG_H

/// Loop contract configurations
struct loop_contract_configt
{
public:
  // Apply loop contracts.
  bool apply_loop_contracts = false;

  // Unwind transformed loops after applying loop contracts or not.
  bool unwind_transformed_loops = true;

  // Check if loop contracts are all side-effect free.
  bool check_side_effect = true;

  std::string to_string() const
  {
    std::string result;
    result += "Apply loop contracts: ";
    result += (apply_loop_contracts ? "yes\n" : "no\n");
    result += "Unwind transformed loops: ";
    result += (unwind_transformed_loops ? "yes\n" : "no\n");
    result += "Check side effect of loop contracts: ";
    result += (check_side_effect ? "yes\n" : "no\n");
    return result;
  }

  bool operator==(const loop_contract_configt &rhs) const
  {
    return apply_loop_contracts == rhs.apply_loop_contracts &&
           unwind_transformed_loops == rhs.unwind_transformed_loops &&
           check_side_effect == rhs.check_side_effect;
  }

  bool operator!=(const loop_contract_configt &rhs) const
  {
    return !(this == &rhs);
  }
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_LOOP_CONTRACT_CONFIG_H
