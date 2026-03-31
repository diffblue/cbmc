/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Periodic SAT Solver Invocation

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with periodic
/// SAT solver invocation every N symex steps

#ifndef CPROVER_GOTO_CHECKER_PERIODIC_INCREMENTAL_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_PERIODIC_INCREMENTAL_SYMEX_CHECKER_H

#include <goto-programs/unwindset.h>

#include <goto-symex/path_storage.h>

#include "goto_symex_property_decider.h"
#include "goto_trace_provider.h"
#include "incremental_goto_checker.h"
#include "symex_bmc.h"
#include "witness_provider.h"

#include <memory>
#include <thread>

/// Performs a multi-path symbolic execution using goto-symex
/// that periodically pauses every N steps
/// and calls a SAT/SMT solver to check the status of the properties
/// after each pause.
class periodic_incremental_symex_checkert : public incremental_goto_checkert,
                                            public goto_trace_providert,
                                            public witness_providert
{
public:
  periodic_incremental_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  /// \copydoc incremental_goto_checkert::operator()(propertiest &properties)
  ///
  /// Note: This operator can handle shrinking and expanding sets of
  ///   properties in repeated invocations.
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
  path_fifot path_storage;
  guard_managert guard_manager;
  unwindsett unwindset;

  /// Symex subclass that pauses every N steps
  class symex_bmc_periodic_stept : public symex_bmct
  {
  public:
    symex_bmc_periodic_stept(
      message_handlert &message_handler,
      const symbol_tablet &outer_symbol_table,
      symex_target_equationt &target,
      const optionst &options,
      path_storaget &path_storage,
      guard_managert &guard_manager,
      unwindsett &unwindset,
      unsigned interval);

    /// Return true if symex can be resumed
    bool from_entry_point_of(
      const get_goto_functiont &get_goto_function,
      symbol_tablet &new_symbol_table);

    /// Return true if symex can be resumed
    bool resume(const get_goto_functiont &get_goto_function);

  protected:
    unsigned step_counter;
    const unsigned step_interval;
    std::size_t last_assertion_count;

    std::unique_ptr<goto_symext::statet> state;

    void symex_step(const get_goto_functiont &get_goto_function, statet &state)
      override;
  };

  symex_bmc_periodic_stept symex;
  bool initial_equation_generated = false;
  bool full_equation_generated = false;
  bool current_equation_converted = false;

  /// Speculative checking state (only active with --speculative-check)
  bool speculative_checking_enabled = false;
  std::unique_ptr<std::thread> speculative_thread;
  bool speculative_sat = false;
  std::string speculative_log_output;
  std::size_t last_speculative_assertion_count = 0;

  goto_symex_property_decidert property_decider;
};

#endif // CPROVER_GOTO_CHECKER_PERIODIC_INCREMENTAL_SYMEX_CHECKER_H
