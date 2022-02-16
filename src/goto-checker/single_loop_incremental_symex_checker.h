/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Incremental Unwinding of a specified Loop

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with incremental
/// unwinding of a specified loop

#ifndef CPROVER_GOTO_CHECKER_SINGLE_LOOP_INCREMENTAL_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_SINGLE_LOOP_INCREMENTAL_SYMEX_CHECKER_H

#include <goto-symex/path_storage.h>

#include <goto-instrument/unwindset.h>

#include "goto_symex_property_decider.h"
#include "goto_trace_provider.h"
#include "incremental_goto_checker.h"
#include "symex_bmc_incremental_one_loop.h"
#include "witness_provider.h"

/// Performs a multi-path symbolic execution using goto-symex
/// that incrementally unwinds a given loop
/// and calls a SAT/SMT solver to check the status of the properties
/// after each iteration.
class single_loop_incremental_symex_checkert : public incremental_goto_checkert,
                                               public goto_trace_providert,
                                               public witness_providert
{
public:
  single_loop_incremental_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  /// \copydoc incremental_goto_checkert::operator()(propertiest &properties)
  ///
  /// Note: This operator can handle shrinking and expanding sets of properties
  ///   in repeated invocations.
  resultt operator()(propertiest &) override;

  goto_tracet build_full_trace() const override;
  goto_tracet build_trace(const irep_idt &) const override;
  goto_tracet build_shortest_trace() const override;
  const namespacet &get_namespace() const override;

  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;

protected:
  abstract_goto_modelt &goto_model;
  symbol_tablet symex_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  path_fifot path_storage; // should go away
  guard_managert guard_manager;
  unwindsett unwindset;
  symex_bmc_incremental_one_loopt symex;
  bool initial_equation_generated = false;
  bool full_equation_generated = false;
  bool current_equation_converted = false;
  goto_symex_property_decidert property_decider;
};

#endif // CPROVER_GOTO_CHECKER_SINGLE_LOOP_INCREMENTAL_SYMEX_CHECKER_H
