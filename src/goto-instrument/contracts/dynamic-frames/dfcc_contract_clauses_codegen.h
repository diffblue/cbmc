/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: February 2023

\*******************************************************************/

/// \file
/// Translates assigns and frees clauses of a function contract or
/// loop contract into goto programs that build write sets or havoc write sets.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_CLAUSES_CODEGEN_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_CONTRACT_CLAUSES_CODEGEN_H

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

class dfcc_contract_clauses_codegent
{
public:
  /// \param goto_model goto model being transformed
  /// \param message_handler used debug/warning/error messages
  /// \param utils utility class for dynamic frames
  /// \param library the contracts instrumentation library
  /// \param spec_functions provides translation methods for assignable set
  /// or freeable set specification functions.
  dfcc_contract_clauses_codegent(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_utilst &utils,
    dfcc_libraryt &library,
    dfcc_spec_functionst &spec_functions);

  /// \brief Generates instructions encoding the \p assigns_clause targets and
  /// adds them to \p dest.
  ///
  /// \details Assumes that all targets in the clause are represented as plain
  /// expressions (i.e. an lambdas expressions introduced for function contract
  /// targets may are already instanciated).
  ///
  /// \param language_mode Mode to use for fresh symbols
  /// \param assigns_clause Sequence of targets to encode
  /// \param dest Destination program
  void gen_spec_assigns_instructions(
    const irep_idt &language_mode,
    const exprt::operandst &assigns_clause,
    goto_programt &dest);

  /// \brief Generates instructions encoding the \p frees_clause targets and
  /// adds them to \p dest.
  ///
  /// \details Assumes that all targets in the clause are represented as plain
  /// expressions (i.e. an lambdas expressions introduced for function contract
  /// targets may are already instanciated).
  ///
  /// \param language_mode Mode to use for fresh symbols
  /// \param frees_clause Sequence of targets to encode
  /// \param dest Destination program
  void gen_spec_frees_instructions(
    const irep_idt &language_mode,
    const exprt::operandst &frees_clause,
    goto_programt &dest);

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_utilst &utils;
  dfcc_libraryt &library;
  dfcc_spec_functionst &spec_functions;
  namespacet ns;

  /// Generates GOTO instructions to build the representation of the given
  /// conditional target group.
  void encode_assignable_target_group(
    const irep_idt &language_mode,
    const conditional_target_group_exprt &group,
    goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// assignable target.
  void encode_assignable_target(
    const irep_idt &language_mode,
    const exprt &target,
    goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// conditional target group.
  void encode_freeable_target_group(
    const irep_idt &language_mode,
    const conditional_target_group_exprt &group,
    goto_programt &dest);

  /// Generates GOTO instructions to build the representation of the given
  /// freeable target.
  void encode_freeable_target(
    const irep_idt &language_mode,
    const exprt &target,
    goto_programt &dest);

  /// Inlines all calls in the given program and checks that the only missing
  /// functions or functions without bodies are built-in functions,
  /// and that no other warnings happened.
  void inline_and_check_warnings(goto_programt &goto_program);
};

#endif
