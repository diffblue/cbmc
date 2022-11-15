/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Generates the body of a wrapper function from a contract
/// for contract checking or contract replacement

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_WRAPPER_PROGRAM_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_WRAPPER_PROGRAM_H

#include <goto-programs/goto_convert_class.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/optional.h>
#include <util/std_expr.h>

#include "dfcc_contract_functions.h"
#include "dfcc_contract_mode.h"

#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class dfcc_instrumentt;
class dfcc_libraryt;
class dfcc_utilst;
class code_with_contract_typet;
class conditional_target_group_exprt;
class function_pointer_obeys_contract_exprt;

/// \brief Generates the body of a wrapper function from a contract
/// specified using requires, requires_contract, assigns, frees, ensures,
/// ensures_contract clauses attached to a function symbol. The desired mode
/// CHECK or REPLACE is given to the constructor of the class.
///
/// \details The body of the wrapper is divided into a number of sections
/// represented as separate goto_programs:
/// - \ref preamble
///  - create is_fresh_set, requires_write_set, ensures_write_set,
///    contract_write_set variables
/// - \ref link_is_fresh
///   - link the is_fresh_set to requires_write_set and ensures_write_set
///   - in REPLACE mode, link the caller_write_set to the contract_write_set
///     so that deallocations and allocations are reflected in the caller
/// - \ref preconditions
///   - evaluate preconditions, checking side effects against requires_write_set
/// - \ref history
///   - declare and snapshot history variables
/// - \ref write_set_checks
///   - populate the contract write set and check it for inclusion against
///     the caller write set if REPLACE mode is selected.
/// - \ref function_call
///   - in CHECK mode
///   ```c
///   CALL retval = foo(params, contract_write_set);
///   ```
///   - in REPLACE mode
///   ```c
///   CALL foo::havoc(contract_write_set);
///   CALL deallocate_freeable(contract_write_set, caller_write_set);
///   ASSIGN retval = nondet
///   ```
/// - \ref link_allocated_caller
///   in REPLACE mode, links the allocated set of the caller to the
///   ensures_write_set, so that allocations performed by is fresh in post
///   conditions get recorded in the caller write set and are considered as
///   assignable for the caller (In CHECK mode, the caller write set comes from
///   the proof harness and is NULL and ignored).
///   ```c
///   CALL link_allocated(ensures_write_set, caller_write_set);
///   ```
/// - \ref link_deallocated_contract
///   links the deallocated set of the contract_write_set
///   to the ensures_write_set, so that was_freed predicates can be evaluated
///   in the post conditions.
///   ```c
///   CALL link_allocated(ensures_write_set, caller_write_set);
///   ```
/// - \ref postconditions
///   - evaluate preconditions, checking side effects against ensures_write_set
/// - \ref postamble
///  - release all object sets and write set variables
///
/// There a private method per type of contract clause, which adds contents
/// encoding the semantics of the clause to the appropriate section when called.
///
/// The public method \ref add_to_dest calls the private methods to populate the
/// sections, and then adds the contents of these sections in order to the
/// given destination program.
class dfcc_wrapper_programt
{
public:
  /// \param contract_mode checking or replacement mode for the contract
  /// \param wrapper_symbol function symbol receiving the generated instructions
  /// \param wrapped_symbol function symbol being checked or replaced
  /// \param contract_functions contains the contract expressions and the
  /// assigns/frees/havoc functions symbols derived from the contract
  /// \param caller_write_set_symbol symbol representing the write set passed
  /// to the wrapper function by its caller.
  /// \param goto_model the goto model being transformed
  /// \param message_handler used for debug/warning/error messages
  /// \param utils utility functions for contracts transformation
  /// \param library the contracts instrumentation library
  /// \param instrument the instrumenter class for goto functions/goto programs
  dfcc_wrapper_programt(
    const dfcc_contract_modet contract_mode,
    const symbolt &wrapper_symbol,
    const symbolt &wrapped_symbol,
    const dfcc_contract_functionst &contract_functions,
    const symbolt &caller_write_set_symbol,
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_instrumentt &instrument);

  /// Adds the whole program to `dest` and the discovered function pointer
  /// contracts `dest_fp_contracts`.
  void add_to_dest(goto_programt &dest, std::set<irep_idt> &dest_fp_contracts);

protected:
  const dfcc_contract_modet contract_mode;
  const symbolt &wrapper_symbol;
  const symbolt &wrapped_symbol;
  const dfcc_contract_functionst &contract_functions;
  const symbolt &contract_symbol;
  const code_with_contract_typet &contract_code_type;
  const symbol_exprt caller_write_set;

  /// Source location with wrapper function name as function name
  const source_locationt wrapper_sl;

  /// Symbol for the return value of the wrapped function
  optionalt<symbol_exprt> return_value_opt;

  /// Symbol for the write set object derived from the contract
  const symbol_exprt contract_write_set;

  /// Symbol for the pointer to the write set object derived from the contract
  const symbol_exprt addr_of_contract_write_set;

  /// Symbol for the write set used to check requires clauses for side effects
  const symbol_exprt requires_write_set;

  /// Symbol for the pointer to the write set used to check requires clauses
  const symbol_exprt addr_of_requires_write_set;

  /// Symbol for the write set used to check ensures clauses for side effects
  const symbol_exprt ensures_write_set;

  /// Symbol for the pointer to the write set used to check ensures clauses
  const symbol_exprt addr_of_ensures_write_set;

  /// Symbol for the object set used to evaluate is_fresh predicates.
  const symbol_exprt is_fresh_set;

  /// Symbol for the pointer to the is_fresh object set.
  const symbol_exprt addr_of_is_fresh_set;

  /// Set of required or ensured contracts for function pointers discovered
  /// when processing the contract of interest.
  std::set<irep_idt> function_pointer_contracts;

  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_instrumentt &instrument;
  namespacet ns;
  goto_convertt converter;

  /// Vector of arguments to use to instantiate the lambdas wrapping the
  /// contract clauses
  exprt::operandst contract_lambda_parameters;

  // The body of a wrapper function is decomposed in different sections.
  // Each type of contract clause may add instructions to multiple sections.
  // The sections then get added to the target program by \ref add_to_dest
  // in the declaration order below.

  goto_programt preamble;
  goto_programt link_is_fresh;
  goto_programt preconditions;
  goto_programt history;
  goto_programt write_set_checks;
  goto_programt function_call;
  goto_programt link_allocated_caller;
  goto_programt link_deallocated_contract;
  goto_programt postconditions;
  goto_programt postamble;

  /// Adds the whole generated program to `dest`, which is meant to be a part of
  /// the body of the `wrapper_symbol`.
  void add_to_dest(goto_programt &dest);

  /// Encodes the empty write set used to check for side effects in requires
  /// - Adds declaration of write set and pointer to write set to \ref preamble
  /// - Adds initialisation function call in \ref preamble
  /// - Adds alloc/deallocation checking assertion in \ref postamble
  /// - Adds release function call in \ref postamble
  void encode_requires_write_set();

  /// Encodes the empty write set used to check for side effects in ensures
  /// - Adds declaration of write set and pointer to write set to \ref preamble
  /// - Adds initialisation function call in \ref preamble
  /// - Adds alloc/deallocation checking assertion in \ref postamble
  /// - Adds release function call in \ref postamble
  void encode_ensures_write_set();

  /// Encodes the write set of the contract being checked/replaced
  /// (populated by calling functions provided in contract_functions)
  /// - Adds declaration of write set and pointer to write set to \ref preamble
  /// - Adds initialisation function call in \ref write_set_checks
  /// - Adds contract::assigns and contract::frees function call
  /// in \ref write_set_checks
  /// - Adds release function call in \ref postamble
  void encode_contract_write_set();

  /// Encodes the object set used to evaluate is fresh predicates,
  /// - Adds declaration of object set and pointer to set to \ref preamble
  /// - Adds initialisation function call in \ref preamble
  /// - Adds release function call in \ref postamble
  void encode_is_fresh_set();

  /// Encodes preconditions, instruments them to check for side effects
  void encode_requires_clauses();

  /// Encodes postconditions, instruments them to check for side effects
  void encode_ensures_clauses();

  /// Encodes the function call section of the wrapper program.
  void encode_function_call();

  /// Creates a checked function call to the wrapped function, passing it the
  /// contract-derived write set as parameter.
  void encode_checked_function_call();

  /// Creates instructions that havoc the contract write set,
  /// create a nondet return value, nondeterministically free the freeable
  /// part of the write set.
  void encode_havoced_function_call();
};

#endif
