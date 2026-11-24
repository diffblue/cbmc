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

#include <util/expr.h>
#include <util/message.h>
#include <util/namespace.h>

#include <goto-programs/goto_functions.h>

class conditional_target_group_exprt;
class dfcc_libraryt;
class goto_modelt;
class goto_programt;

/// Translates assigns and frees clauses of a function contract or
/// loop contract into GOTO programs that build write sets or havoc write sets.
class dfcc_contract_clauses_codegent
{
public:
  /// \param goto_model GOTO model being transformed
  /// \param message_handler Used debug/warning/error messages
  /// \param library The contracts instrumentation library
  dfcc_contract_clauses_codegent(
    goto_modelt &goto_model,
    message_handlert &message_handler,
    dfcc_libraryt &library);

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

  /// \brief Records the bodies of the functions of the GOTO model as they are
  /// now, before any of them gets instrumented.
  ///
  /// \details The calls in the instructions generated from then on, e.g., to a
  /// function in the condition of a conditional target, are inlined using the
  /// recorded bodies. An instrumented function takes a write set as additional
  /// parameter, which the generated calls do not pass, and contains calls to
  /// write set checks, which must not be part of the generated instructions.
  /// Loop contracts are encoded while functions are being instrumented, so
  /// that the functions called in their clauses may already be instrumented.
  void record_function_bodies();

protected:
  goto_modelt &goto_model;
  message_handlert &message_handler;
  messaget log;
  dfcc_libraryt &library;
  namespacet ns;

  /// The function bodies recorded by record_function_bodies
  goto_functionst function_bodies;
  bool function_bodies_recorded = false;

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
