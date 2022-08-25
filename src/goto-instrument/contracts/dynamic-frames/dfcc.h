/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Main class orchestrating the the whole program transformation
/// for function contracts with Dynamic Frame Condition Checking (DFCC)
///
/// Contracts must be expressed in DSL-style, i.e. as contract clauses attached
/// to the function declaration at the C level.
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

#define FLAG_DFCC "dfcc"
#define OPT_DFCC "(" FLAG_DFCC "):"
// clang-format off
#define HELP_DFCC                                                              \
  "--dfcc               activate dynamic frame condition checking for function"\
  "                     contracts using given function as entry point"
// clang-format on

/// Applies function contracts and loop contracts transformation to GOTO model,
/// using the dynamic frame condition checking approach.
///
/// This function requires that the contract associated to function `foo` is
/// found in the symbol table as symbol `contract::foo`.
///
/// \param goto_model GOTO model to transform
/// \param harness_id proof harness name, must be the entry point of the model
/// \param to_check set of functions to check against their contract
/// (must contain at most one element)
/// \param to_replace set of functions to replace with their contract
/// \param apply_loop_contracts apply loop contract transformations iff true
/// \param exclude_from_nondet_static set of symbols to exclude when havocing
/// static program symbols.
/// \param log logger to use for debug/warning/error messages
void dfcc(
  goto_modelt &goto_model,
  const std::string &harness_id,
  const std::set<std::string> &to_check,
  const std::set<std::string> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &exclude_from_nondet_static,
  messaget &log);

/// Applies function contracts and loop contracts transformation to GOTO model,
/// using the dynamic frame condition checking approach.
///
/// Functions to check/replace are explicitly mapped to contracts.
/// When checking function `foo` against contract `bar`, we require the
/// actual contract symbol to exist as `contract::bar` in the symbol table.
///
/// \param goto_model GOTO model to transform
/// \param harness_id proof harness name, must be the entry point of the model
/// \param to_check functions-to-contract mapping for contract checking
/// (must contain at most one element)
/// \param to_replace functions-to-contract mapping for replacement
/// \param apply_loop_contracts apply loop contract transformations iff true
/// \param exclude_from_nondet_static set of symbols to exclude when havocing
/// static program symbols.
/// \param log logger to use for debug/warning/error messages
void dfcc(
  goto_modelt &goto_model,
  const std::string &harness_id,
  const std::map<std::string, std::string> &to_check,
  const std::map<std::string, std::string> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &exclude_from_nondet_static,
  messaget &log);

class dfcct
{
public:
  /// Class constructor
  /// \param goto_model GOTO model to transform
  /// \param log logger to use for debug/warning/error messages
  dfcct(goto_modelt &goto_model, messaget &log);

  /// Applies function contracts and loop contracts transformation to GOTO model
  /// using the dynamic frame condition checking approach.
  ///
  /// Functions to check/replace are explicitly mapped to contracts.
  /// When checking function `foo` against contract `bar`, we require the
  /// actual contract symbol to exist as `contract::bar` in the symbol table.
  ///
  /// \param harness_id proof harness name, must be the entry point of the model
  /// \param to_check functions-to-contract mapping for contract checking
  /// (must contain at most one element)
  /// \param to_replace functions-to-contract mapping for replacement
  /// \param apply_loop_contracts apply loop contract transformations iff true
  /// \param exclude_from_nondet_static set of symbols to exclude when havocing
  /// static program symbols.
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
  void transform_goto_model(
    const std::string &harness_id,
    const std::map<std::string, std::string> &to_check,
    const std::map<std::string, std::string> &to_replace,
    const bool apply_loop_contracts,
    const std::set<std::string> &to_exclude_from_nondet_static);

protected:
  goto_modelt &goto_model;
  messaget &log;
  message_handlert &message_handler;

  // hold the global state of the transformation (caches etc.)
  dfcc_utilst utils;
  dfcc_libraryt library;
  namespacet ns;
  dfcc_instrumentt instrument;
  dfcc_spec_functionst spec_functions;
  dfcc_dsl_contract_handlert dsl_contract_handler;
  dfcc_swap_and_wrapt swap_and_wrap;

  /// Maps wrapper function to the wrapped function.
  /// Caching prevents wrapping more than once.
  static std::map<irep_idt, irep_idt> wrapped_functions_cache;

  /// Tracks the maximum number of targets in any assigns clause handled in the
  /// transformation (used to specialize/unwind loops in DFCC library functions)
  int max_assigns_clause_size;

  /// Checks preconditions on \ref check_transform_goto_model arguments
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
  /// - all symbols of `exclude_from_nondet_static` exist in the model.
  void check_transform_goto_model_preconditions(
    const std::string &harness_id,
    const std::map<std::string, std::string> &to_check,
    const std::map<std::string, std::string> &to_replace,
    const bool apply_loop_contracts,
    const std::set<std::string> &exclude_from_nondet_static);

  /// Partitions the given vector `symbols` into 4 sets of function symbols.
  void partition_function_symbols(
    const std::vector<irep_idt> &symbols,
    std::set<irep_idt> &pure_contract_symbols,
    std::set<irep_idt> &assignable_t_symbols,
    std::set<irep_idt> &freeable_t_symbols,
    std::set<irep_idt> &other_symbols);
};

#endif
