/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \defgroup contracts-module Code Contracts

/// \defgroup dfcc-module Dynamic Frame Condition Checking (DFCC)
/// \ingroup contracts-module

/// \file
/// \ingroup dfcc-module
///
/// \brief Main class orchestrating the the whole program transformation
/// for function contracts with Dynamic Frame Condition Checking (DFCC)
///
/// All functions of the model are extended with a ghost parameter representing
/// a dynamic frame and all their assignments are instrumented and checked
/// against the dynamic frame parameter.
///
/// Targets specified by assigns clauses and frees clauses of the contracts
/// are reified into dynamic data structures built by ghost code embedded in the
/// program and are propagated through function calls and function pointer calls
/// as ghost call arguments.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_H

#include <util/irep.h>
#include <util/message.h>

#include "dfcc_contract_handler.h"
#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_swap_and_wrap.h"
#include "dfcc_utils.h"

#include <map>
#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class symbolt;
class conditional_target_group_exprt;
class cfg_infot;
class optionst;

#define FLAG_DFCC "dfcc"
#define OPT_DFCC "(" FLAG_DFCC "):"

// clang-format off
#define HELP_DFCC                                                              \
  "--dfcc             activate dynamic frame condition checking for function\n"\
  "                   contracts using given function as entry point"
// clang-format on

// clang-format off
#define FLAG_ENFORCE_CONTRACT_REC "enforce-contract-rec"
#define OPT_ENFORCE_CONTRACT_REC "(" FLAG_ENFORCE_CONTRACT_REC "):"
#define HELP_ENFORCE_CONTRACT_REC                                              \
  " --enforce-contract-rec <fun>  wrap fun with an assertion of its contract\n"\
  "                               and assume recursive calls to fun satisfy \n"\
  "                               the contract"
// clang-format on

/// \ingroup dfcc-module
/// \brief Applies function contracts transformation to GOTO model,
/// using the dynamic frame condition checking approach.
///
/// \pre This function requires that the contract associated to function `foo`
/// exists in the symbol table as symbol `contract::foo`.
///
/// \param options CLI options (used to lookup options for language config when
/// re-defining the model's entry point)
/// \param goto_model GOTO model to transform
/// \param harness_id proof harness name, must be the entry point of the model
/// \param to_check function to check against its contract
/// \param allow_recursive_calls Allow the checked function to be recursive
/// \param to_replace set of functions to replace with their contract
/// \param apply_loop_contracts apply loop contract transformations iff true
/// \param to_exclude_from_nondet_static set of symbols to exclude when havocing
/// static program symbols.
/// \param message_handler used for debug/warning/error messages
void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const optionalt<irep_idt> &to_check,
  const bool allow_recursive_calls,
  const std::set<irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &to_exclude_from_nondet_static,
  message_handlert &message_handler);

/// \ingroup dfcc-module
/// \brief Applies function contracts and loop contracts transformation to GOTO
/// model, using the dynamic frame condition checking approach.
///
/// Functions to check/replace are explicitly mapped to contracts.
/// When checking function `foo` against contract `bar`, we require the
/// actual contract symbol to exist as `contract::bar` in the symbol table.
///
/// \param options CLI options (used to lookup options for language config when
/// re-defining the model's entry point)
/// \param goto_model GOTO model to transform
/// \param harness_id Proof harness name, must be the entry point of the model
/// \param to_check (function,contract) pair for contract checking
/// \param allow_recursive_calls Allow the checked function to be recursive
/// \param to_replace Functions-to-contract mapping for replacement
/// \param apply_loop_contracts Spply loop contract transformations iff true
/// \param to_exclude_from_nondet_static Set of symbols to exclude when havocing
/// static program symbols.
/// \param message_handler used for debug/warning/error messages
void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const optionalt<std::pair<irep_idt, irep_idt>> &to_check,
  const bool allow_recursive_calls,
  const std::map<irep_idt, irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &to_exclude_from_nondet_static,
  message_handlert &message_handler);

/// \ingroup dfcc-module
/// \brief Entry point into the contracts transformation
class dfcct
{
public:
  /// Class constructor
  /// \param options CLI options (used to lookup options for language config
  /// when re-defining the model's entry point)
  /// \param goto_model GOTO model to transform
  /// \param harness_id Proof harness name, must be the entry point of the model
  /// \param to_check (function,contract) pair for contract checking
  /// \param allow_recursive_calls Allow the checked function to be recursive
  /// \param to_replace functions-to-contract mapping for replacement
  /// \param apply_loop_contracts apply loop contract transformations iff true
  /// havocing static program symbols.
  /// \param message_handler used for debug/warning/error messages
  /// \param to_exclude_from_nondet_static set of symbols to exclude when
  dfcct(
    const optionst &options,
    goto_modelt &goto_model,
    const irep_idt &harness_id,
    const optionalt<std::pair<irep_idt, irep_idt>> &to_check,
    const bool allow_recursive_calls,
    const std::map<irep_idt, irep_idt> &to_replace,
    const bool apply_loop_contracts,
    message_handlert &message_handler,
    const std::set<std::string> &to_exclude_from_nondet_static);

  /// Applies function contracts and loop contracts transformation to GOTO model
  /// using the dynamic frame condition checking approach.
  ///
  /// Functions to check/replace are explicitly mapped to contracts.
  /// When checking function `foo` against contract `bar`, we require the
  /// actual contract symbol to exist as `contract::bar` in the symbol table.
  ///
  /// Transformation steps:
  /// - check preconditions on existence and absence of clash between harness,
  /// functions and contract symbols parameters.
  /// - link the goto model to the standard library
  /// - instrument the harness function.
  /// - partition function symbols of the model into
  ///   - `contract::` symbols
  ///   - assigns/frees clause specification functions (not instrumented)
  ///   - all other functions (instrumented)
  /// - swap-and-wrap/instrument functions to check with their contract
  /// - swap-and-wrap/instrument functions to replace with their contract
  /// - swap-and-wrap all discovered function pointer contracts with themselves
  ///   (replacement mode)
  /// - instrument all remaining functions GOTO model
  /// - (this includes standard library functions).
  /// - specialise the instrumentation functions by unwiding loops they contain
  /// to the maximum size of any assigns clause involved in the model.
  void transform_goto_model();

protected:
  const optionst &options;
  goto_modelt &goto_model;
  const irep_idt &harness_id;
  const optionalt<std::pair<irep_idt, irep_idt>> &to_check;
  const bool allow_recursive_calls;
  const std::map<irep_idt, irep_idt> &to_replace;
  const bool apply_loop_contracts;
  const std::set<std::string> &to_exclude_from_nondet_static;
  message_handlert &message_handler;
  messaget log;

  // hold the global state of the transformation (caches etc.)
  dfcc_utilst utils;
  dfcc_libraryt library;
  namespacet ns;
  dfcc_instrumentt instrument;
  dfcc_spec_functionst spec_functions;
  dfcc_contract_handlert contract_handler;
  dfcc_swap_and_wrapt swap_and_wrap;

  /// Tracks the maximum number of targets in any assigns clause handled in the
  /// transformation (used to specialize/unwind loops in DFCC library functions)
  std::size_t max_assigns_clause_size;

  // partition the set of functions of the goto_model
  std::set<irep_idt> pure_contract_symbols;
  std::set<irep_idt> other_symbols;
  std::set<irep_idt> function_pointer_contracts;

  /// Checks preconditions on arguments of \ref transform_goto_model.
  ///
  /// The preconditions are:
  /// - The harness function exists in the model and has a body,
  /// - The model's entry point is the harness function,
  /// - The harness function is distinct from any checked or replaced function,
  /// - The harness function is distinct from any contract,
  /// - All function to check exist and have a body available,
  /// - All function to replace exist (body is not necessary),
  /// - All contracts to check or replace exist as pure contract symbols,
  /// - The checked function cannot be also replaced,
  /// - compiler built-ins or `__CPROVER_*` functions cannot be checked against
  /// a contract (because they cannot be instrumented),
  /// - all symbols of `to_exclude_from_nondet_static` exist in the model.
  void check_transform_goto_model_preconditions();

  /// Partitions the function symbols of the symbol table into pure contracts
  /// and other function symbols symbols.
  void partition_function_symbols(
    std::set<irep_idt> &pure_contract_symbols,
    std::set<irep_idt> &other_symbols);

  void link_model_and_load_dfcc_library();
  void instrument_harness_function();
  void wrap_checked_function();
  void wrap_replaced_functions();
  void wrap_discovered_function_pointer_contracts();
  void instrument_other_functions();

  /// \brief Re-initialise the GOTO model.
  ///
  /// \details
  /// The new entry point must be the proof harness function specified for
  /// instrumentation.
  ///
  /// The "initialize" (aka INITIALIZE_FUNCTION) is the function that assigns
  /// initial values to all statics of the model;
  ///
  /// The initialize function must do the following:
  /// - assign a nondet value to all statics of the user program
  /// - assign the specified initial value to all instrumentation statics
  /// - add an entry in the static unbounded map of instrumented functions
  /// for each instrumented function
  ///
  /// A call to `nondet_static` will re-generate the initialize function with
  /// nondet values. The intrumentation statics will not get nondet initialised
  /// by virtue of being tagged with ID_C_no_nondet_initialization.
  ///
  /// However, nondet_static expects instructions to be either function calls
  /// or assignments with a symbol_exprt LHS.
  /// Since entries for the instrumented function maps are not symbol_exprts but
  /// index_exprts they need to be moved to the harness function.
  ///
  /// The "start" function (aka goto_functionst::entry_point()) is the
  /// function from which SymEx starts.
  ///
  /// The start function must do the following:
  /// - call the initialize function,
  /// - generate nondet values for the arguments of the proof harness function
  /// - call the harness function with said nondet arguments
  ///
  /// All of which can be done using a call to `generate_ansi_c_start_function`,
  /// assuming the initialize function is already available in the symbol table.
  ///
  /// So we do the following:
  /// - regenerate the "initialize" function
  /// - call nondet_static
  /// - add extra instructions at the end of the harness function for the
  /// instrumented functions map
  /// - call generate_ansi_c_start_function
  /// Make all user-defined statics nondet.
  /// Other statics added by the instrumentation will be unaffected because they
  /// are tagged with ID_C_no_nondet_initialization when created
  /// Update statics and static function maps
  void reinitialize_model();
};

#endif
