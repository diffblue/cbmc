/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Specialisation of \ref dfcc_contract_handlert for contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_HANDLER_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_HANDLER_H

#include <goto-programs/goto_convert_class.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/optional.h>
#include <util/std_expr.h>

#include "dfcc_contract_functions.h"

#include <set>

class goto_modelt;
class message_handlert;
class dfcc_libraryt;
class dfcc_utilst;
class dfcc_instrumentt;
class dfcc_lift_memory_predicatest;
class dfcc_spec_functionst;
class dfcc_contract_clauses_codegent;
class code_with_contract_typet;
class conditional_target_group_exprt;

/// A contract is represented by a function declaration or definition
/// with contract clauses attached to its signature:
///
/// ```
/// ret_t foo(foo_params)
/// __CPROVER_requires(R)
/// __CPROVER_assigns(A)
/// __CPROVER_frees(F)
/// __CPROVER_ensures(E)
/// { foo_body; } [optional]
/// ```
///
/// In the symbol table, this declaration creates two symbols:
/// - `ret_t foo(foo_params)` which represents the function (with optional body)
/// - `ret_t contract::foo(foo_params)` which represents the pure contract part
/// and carries the contract clauses in its `.type` attribute.
///
/// This class allows, given a contract name `foo`, to lookup the symbol
/// `contract::foo` and translate its assigns and frees clauses into GOTO
/// functions that build dynamic frames at runtime (stored in an object of
/// type \ref dfcc_contract_functionst).
///
/// Translation results are cached so it is safe to call
/// `get_contract_functions` several times.
///
/// This class also implements the \ref dfcc_contract_handlert interface
/// and allows to generate instructions modelling contract checking and
/// contract replacement.
class dfcc_contract_handlert
{
public:
  dfcc_contract_handlert(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument,
    dfcc_lift_memory_predicatest &memory_predicates,
    dfcc_spec_functionst &spec_functions,
    dfcc_contract_clauses_codegent &contract_clauses_codegen);

  /// Adds instructions in `dest` modeling contract checking, assuming
  /// that `ret_t wrapper_id(params)` is the function receiving
  /// the instructions.
  ///
  /// \param[in] contract_mode checking or replacement mode
  /// \param[in] wrapper_id name of function receiving the instructions
  /// \param[in] wrapped_id name of function that is being checked/replaced
  /// \param[in] contract_id name of the contract to check
  /// \param[in] wrapper_write_set_symbol write_set parameter of the wrapper
  /// \param[out] dest destination program where instructions are added
  /// (should eventually become the body of wrapper_id)
  /// \param[out] function_pointer_contracts list of contracts found in either
  /// pre or post conditions of the processed contract. These contracts need to
  /// be swapped_and_wrapped in replacement mode if they are not already.
  void add_contract_instructions(
    const dfcc_contract_modet contract_mode,
    const irep_idt &wrapper_id,
    const irep_idt &wrapped_id,
    const irep_idt &contract_id,
    const symbolt &wrapper_write_set_symbol,
    goto_programt &dest,
    std::set<irep_idt> &function_pointer_contracts);

  /// Returns the size assigns clause of the given contract in number of targets
  const std::size_t get_assigns_clause_size(const irep_idt &contract_id);

  /// Searches for a symbol named "contract::contract_id" in the symbol table.
  /// If the "contract::contract_id" is found and \p function_id_opt is present,
  /// type signature compatibility is checked between the contract and
  /// the function, and an exception is thrown if they are incompatible.
  /// If the symbol was not found and \p function_id_opt was provided,
  /// the function is used as a template to derive a new default contract with
  /// empty requires, empty assigns, empty frees, empty ensures clauses.
  /// If the symbol was not found and \p function_id_opt was not provided, a
  /// PRECONDITION is triggered.
  const symbolt &get_pure_contract_symbol(
    const irep_idt &contract_id,
    const optionalt<irep_idt> function_id_opt = {});

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  dfcc_lift_memory_predicatest &memory_predicates;
  dfcc_spec_functionst &spec_functions;
  dfcc_contract_clauses_codegent &contract_clauses_codegen;
  namespacet ns;

  // Caches the functions generated from contracts
  static std::map<irep_idt, dfcc_contract_functionst> contract_cache;

  /// Returns the `dfcc_contract_functionst` object for the given contract
  /// from the cache, creates it if it does not exists.
  const dfcc_contract_functionst &
  get_contract_functions(const irep_idt &contract_id);

  /// \brief Throws an error if the type signatures are not compatible
  /// \param contract_id name of the function that carries the contract
  /// \param contract_type code_type of contract_id
  /// \param pure_contract_id name of the pure contract symbol for contract_id
  /// \param pure_contract_type code_type of pure_contract_id
  void check_signature_compat(
    const irep_idt &contract_id,
    const code_typet &contract_type,
    const irep_idt &pure_contract_id,
    const code_typet &pure_contract_type);
};

#endif
