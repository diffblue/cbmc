/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Specialisation of \ref dfcc_contract_interfacet for DSL-style contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_DSL_CONTRACT_HANDLER_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_DSL_CONTRACT_HANDLER_H

#include <goto-programs/goto_convert_class.h>

#include <util/namespace.h>
#include <util/optional.h>
#include <util/std_expr.h>

#include "dfcc_contract_handler.h"
#include "dfcc_dsl_contract_functions.h"

#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class dfcc_libraryt;
class dfcc_utilst;
class dfcc_instrumentt;
class dfcc_spec_functionst;
class code_with_contract_typet;
class conditional_target_group_exprt;
class function_pointer_obeys_contract_exprt;

/// A DSL-style contract is represented by a function declaration or definition
/// with contract clauses attached to its signature:
///
/// ```
/// ret_t foo(foo_params)
/// __CPROVER_requires(R)
/// __CPROVER_requires_contract(ptr, contract)
/// __CPROVER_assigns(A)
/// __CPROVER_frees(F)
/// __CPROVER_ensures(E)
/// __CPROVER_ensures_contract(ptr, contract)
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
class dfcc_dsl_contract_handlert : public dfcc_contract_handlert
{
public:
  dfcc_dsl_contract_handlert(
    goto_modelt &goto_model,
    messaget &log,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument,
    dfcc_spec_functionst &spec_functions);

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
    std::set<irep_idt> &function_pointer_contracts) override;

  /// Returns the size assigns clause of the given contract in number of targets
  const int get_assigns_clause_size(const irep_idt &contract_id) override;

  /// Searches for a symbol named "contract::contract_id" that has a type
  /// signature compatible with that of "contract_id", or creates an empty one
  /// if it does not exist.
  /// Returns true if found or created, throws an exception if
  /// "contract::contract_id" already exists but has signature incompatible
  /// with that of "contract_id".
  const bool pure_contract_symbol_exists(const irep_idt &contract_id);

protected:
  goto_modelt &goto_model;
  messaget &log;
  message_handlert &message_handler;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  dfcc_spec_functionst &spec_functions;
  namespacet ns;

  // Caches the functions generated from DSL contracts
  static std::map<irep_idt, dfcc_dsl_contract_functionst> contract_cache;

  /// Searches for a symbol named "contract::contract_id" in the symbol table.
  ///
  /// If a symbol "contract::contract_id" was found and its type signature is
  /// compatible with that of "contract_id" a pointer to the symbol is returned.
  ///
  /// If a symbol "contract::contract_id" was found but its type signature is
  /// not compatible with that of "contract_id" an exception is thrown.
  ///
  /// If a symbol "contract::contract_id" was found, a fresh symbol representing
  /// a contract with empty clauses is inserted in the symbol table and a
  /// pointer to that symbol is returned.
  const symbolt *get_pure_contract_symbol_ptr(const irep_idt &contract_id);

  /// Searches for a symbol named "contract::contract_id" in the symbol table.
  ///
  /// If a symbol "contract::contract_id" was found and its type signature is
  /// compatible with that of "contract_id" a reference to the symbol is
  /// returned.
  ///
  /// If a symbol "contract::contract_id" was found but its type signature is
  /// not compatible with that of "contract_id" an exception is thrown.
  ///
  /// If a symbol "contract::contract_id" was found, a fresh symbol representing
  /// a contract with empty clauses is inserted in the symbol table and a
  /// reference to that symbol is returned.
  const symbolt &get_pure_contract_symbol(const irep_idt &contract_id);

  /// Returns the `dfcc_dsl_contract_functionst` object for the given contract
  /// from the cache, creates it if it does not exists.
  const dfcc_dsl_contract_functionst &
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
