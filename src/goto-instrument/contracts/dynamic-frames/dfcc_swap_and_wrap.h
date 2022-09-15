/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Given a function_id and contract_id, swaps its body to a function
/// with a fresh mangled name, instruments it for dynamic frame condition
/// checking, and replaces the original function's body with instructions
/// encoding contract checking against the mangled function,
/// or contract replacement.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_SWAP_AND_WRAP_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_SWAP_AND_WRAP_H
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_convert_functions.h>

#include "dfcc_contract_handler.h"
#include "dfcc_dsl_contract_handler.h"
#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_utils.h"

#include <map>
#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;
class cfg_infot;

class dfcc_swap_and_wrapt
{
public:
  dfcc_swap_and_wrapt(
    goto_modelt &goto_model,
    messaget &log,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument,
    dfcc_spec_functionst &spec_functions,
    dfcc_contract_handlert &contract_handler);

  void swap_and_wrap(
    const dfcc_contract_modet contract_mode,
    const irep_idt &function_id,
    const irep_idt &contract_id,
    std::set<irep_idt> &function_pointer_contracts,
    bool allow_recursive_calls = false);

  /// Adds the set of swapped functions to dest
  void get_swapped_functions(std::set<irep_idt> &dest) const;

protected:
  goto_modelt &goto_model;
  messaget &log;
  message_handlert &message_handler;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  dfcc_spec_functionst &spec_functions;
  dfcc_contract_handlert &contract_handler;
  namespacet ns;

  /// remember all functions that were swapped/wrapped and in which mode
  static std::map<irep_idt, std::pair<irep_idt, dfcc_contract_modet>> cache;

  /// Swaps-and-wraps the given `function_id` in a wrapper function that
  /// checks the given `contract_id`.
  void check_contract(
    const irep_idt &function_id,
    const irep_idt &contract_id,
    std::set<irep_idt> &function_pointer_contracts,
    bool allow_recursive_calls);

  /// Swaps-and-wraps the given `function_id` in a wrapper function that
  /// models the abstract behaviour of contract `contract_id`.
  void replace_with_contract(
    const irep_idt &function_id,
    const irep_idt &contract_id,
    std::set<irep_idt> &function_pointer_contracts);
};
#endif
