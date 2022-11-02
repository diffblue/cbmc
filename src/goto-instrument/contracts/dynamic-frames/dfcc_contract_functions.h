/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Translates assigns and frees clauses of a function contract into goto
/// functions that allow to build and havoc write sets dynamically.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_FUNCTIONS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_FUNCTIONS_H

#include <goto-programs/goto_convert_class.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/optional.h>
#include <util/std_expr.h>

#include "dfcc_contract_mode.h"

#include <set>

class goto_modelt;
class message_handlert;
class dfcc_libraryt;
class dfcc_utilst;
class dfcc_spec_functionst;
class code_with_contract_typet;
class conditional_target_group_exprt;
class function_pointer_obeys_contract_exprt;

/// Generates GOTO functions modelling a contract assigns and frees clauses.
///
/// The generated functions are the following.
///
/// Populates write_set_to_fill with targets of the assigns clause
/// checks its own body against write_set_to_check:
/// ```c
/// void contract_id::assigns(
///     function-params,
///     write_set_to_fill,
///     write_set_to_check);
/// ```
/// Havocs the targets specified in the assigns clause, assuming
/// write_set_to_havoc is a snapshot created using contract_id::assigns:
/// ```c
/// void contract_id::assigns::havoc(write_set_to_havoc);
/// ```
/// Populates write_set_to_fill with targets of the frees clause
/// checks its own body against write_set_to_check:
/// ```c
/// void contract_id::frees(
///     function-params,
///     write_set_to_fill,
///     write_set_to_check);
/// ```
class dfcc_contract_functionst
{
public:
  /// \param pure_contract_symbol the contract to generate code from
  /// \param goto_model goto model being transformed
  /// \param message_handler used debug/warning/error messages
  /// \param utils utility class for dynamic frames
  /// \param library the contracts instrumentation library
  /// \param spec_functions provides translation methods for assignable set
  /// or freeable set specification functions.
  dfcc_contract_functionst(
    const symbolt &pure_contract_symbol,
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_spec_functionst &spec_functions);

  /// Returns the contract::assigns function symbol
  const symbolt &get_spec_assigns_function_symbol() const;

  /// Returns the contract::assigns::havoc function symbol
  const symbolt &get_spec_assigns_havoc_function_symbol() const;

  /// Returns the contract::frees function symbol
  const symbolt &get_spec_frees_function_symbol() const;

  /// Returns the maximum number of targets in the assigns clause
  const std::size_t get_nof_assigns_targets() const;

  /// Returns the maximum number of targets in the frees clause
  const std::size_t get_nof_frees_targets() const;

  /// The function symbol carrying the contract
  const symbolt &pure_contract_symbol;

  /// The code_with_contract_type carrying the contract clauses
  const code_with_contract_typet &code_with_contract;

  /// Identifier of the contract::assigns function
  const irep_idt spec_assigns_function_id;

  /// Identifier of the contract::assigns::havoc function
  const irep_idt spec_assigns_havoc_function_id;

  /// Identifier of the contract::frees function
  const irep_idt spec_frees_function_id;

  /// Language mode of the contract symbol
  const irep_idt &language_mode;

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_spec_functionst &spec_functions;
  namespacet ns;
  std::size_t nof_assigns_targets;
  std::size_t nof_frees_targets;

  /// Translates the contract's assigns clause to a GOTO function that uses the
  /// `assignable`, `object_upto`, `object_from`, object_whole` built-ins to
  /// express targets.
  void gen_spec_assigns_function();

  /// Translates the contract's frees clause to a GOTO function that uses the
  /// `freeable` built-in to express targets.
  void gen_spec_frees_function();

  /// Generates GOTO instructions to build the representation of the given
  /// conditional target group.
  void encode_assignable_target_group(
    const conditional_target_group_exprt &group,
    goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// assignable target.
  void encode_assignable_target(const exprt &target, goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// conditional target group.
  void encode_freeable_target_group(
    const conditional_target_group_exprt &group,
    goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// freeable target.
  void encode_freeable_target(const exprt &target, goto_programt &dest);

  /// Inlines the given function and checks that the only missign functions
  /// or no body functions are front-end
  // void or __CPROVER_freeable_t functions,
  /// and that no other warnings happened.
  void inline_and_check_warnings(const irep_idt &function_id);
};

#endif
