/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Concurrent SAT Solving

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with concurrent
/// SAT solving in a separate thread

#ifndef CPROVER_GOTO_CHECKER_CONCURRENT_INCREMENTAL_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_CONCURRENT_INCREMENTAL_SYMEX_CHECKER_H

#include <goto-programs/unwindset.h>

#include <goto-symex/path_storage.h>

#include "goto_symex_property_decider.h"
#include "goto_trace_provider.h"
#include "incremental_goto_checker.h"
#include "symex_bmc.h"
#include "witness_provider.h"

#include <condition_variable>
#include <exception>
#include <memory>
#include <mutex>
#include <thread>

/// Performs a multi-path symbolic execution using goto-symex
/// in a separate thread while the main thread runs the SAT solver.
/// The symex thread pauses every N steps and hands off new equation
/// steps to the solver thread via mutex and condition variable
/// synchronization.
class concurrent_incremental_symex_checkert : public incremental_goto_checkert,
                                              public goto_trace_providert,
                                              public witness_providert
{
public:
  concurrent_incremental_symex_checkert(
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

  /// Symex subclass that pauses every N steps for concurrent solving
  class symex_bmc_concurrent_stept : public symex_bmct
  {
  public:
    symex_bmc_concurrent_stept(
      message_handlert &message_handler,
      const symbol_tablet &outer_symbol_table,
      symex_target_equationt &target,
      const optionst &options,
      path_storaget &path_storage,
      guard_managert &guard_manager,
      unwindsett &unwindset,
      unsigned interval);

    /// Start symex from program entry point.
    /// \return true if symex can be resumed (was paused)
    bool from_entry_point_of(
      const get_goto_functiont &get_goto_function,
      symbol_tablet &new_symbol_table);

    /// Resume symex after a pause.
    /// \return true if symex can be resumed (was paused again)
    bool resume(const get_goto_functiont &get_goto_function);

  protected:
    unsigned step_counter;
    const unsigned step_interval;

    std::unique_ptr<goto_symext::statet> state;

    void symex_step(const get_goto_functiont &get_goto_function, statet &state)
      override;
  };

  symex_bmc_concurrent_stept symex;
  bool initial_equation_generated = false;
  bool full_equation_generated = false;
  bool current_equation_converted = false;
  goto_symex_property_decidert property_decider;

  /// Thread running symbolic execution concurrently
  std::unique_ptr<std::thread> symex_thread;

  /// Shared synchronization state between symex and solver threads.
  /// Pipelined: symex is signaled to resume before solve() so it runs
  /// concurrently with SAT solving. After solve() returns, the solver
  /// waits for symex to pause, then the original bottom-of-loop
  /// signal/wait handles the next iteration's conversion phase.
  struct sync_statet
  {
    std::mutex mtx;
    std::condition_variable cv;
    bool symex_paused = false;
    bool symex_done = false;
    bool solver_done = false;
    bool stop_symex = false;
    std::exception_ptr symex_exception;
  };

  sync_statet sync;
};

#endif // CPROVER_GOTO_CHECKER_CONCURRENT_INCREMENTAL_SYMEX_CHECKER_H
