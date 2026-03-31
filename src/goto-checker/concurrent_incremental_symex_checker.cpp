/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Concurrent SAT Solving

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with concurrent
/// SAT solving in a separate thread

#include "concurrent_incremental_symex_checker.h"

#include <util/ui_message.h>

#include "bmc_util.h"
#include "counterexample_beautification.h"

#include <thread>

// --- symex_bmc_concurrent_stept implementation ---

concurrent_incremental_symex_checkert::symex_bmc_concurrent_stept::
  symex_bmc_concurrent_stept(
    message_handlert &message_handler,
    const symbol_tablet &outer_symbol_table,
    symex_target_equationt &target,
    const optionst &options,
    path_storaget &path_storage,
    guard_managert &guard_manager,
    unwindsett &unwindset,
    unsigned interval)
  : symex_bmct(
      message_handler,
      outer_symbol_table,
      target,
      options,
      path_storage,
      guard_manager,
      unwindset),
    step_counter(0),
    step_interval(interval)
{
}

void concurrent_incremental_symex_checkert::symex_bmc_concurrent_stept::
  symex_step(const get_goto_functiont &get_goto_function, statet &state)
{
  symex_bmct::symex_step(get_goto_function, state);

  ++step_counter;
  if(step_counter >= step_interval)
  {
    should_pause_symex = true;
    step_counter = 0;
  }
}

bool concurrent_incremental_symex_checkert::symex_bmc_concurrent_stept::
  from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table)
{
  state = initialize_entry_point_state(get_goto_function);

  new_symbol_table = symex_with_state(*state, get_goto_function);

  return should_pause_symex;
}

bool concurrent_incremental_symex_checkert::symex_bmc_concurrent_stept::resume(
  const get_goto_functiont &get_goto_function)
{
  should_pause_symex = false;

  state->symbol_table = symex_with_state(*state, get_goto_function);

  return should_pause_symex;
}

// --- concurrent_incremental_symex_checkert implementation ---

concurrent_incremental_symex_checkert::concurrent_incremental_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : incremental_goto_checkert(options, ui_message_handler),
    goto_model(goto_model),
    ns(goto_model.get_symbol_table(), symex_symbol_table),
    equation(ui_message_handler),
    symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      path_storage,
      guard_manager,
      unwindset,
      static_cast<unsigned>(
        options.get_signed_int_option("incremental-check-interval"))),
    property_decider(options, ui_message_handler, equation, ns)
{
  unwindset.parse_unwind(options.get_option("unwind"));
  unwindset.parse_unwindset(
    options.get_list_option("unwindset"), goto_model, ui_message_handler);

  // Freeze all symbols if we are using a prop_conv_solvert
  prop_conv_solvert *prop_conv_solver = dynamic_cast<prop_conv_solvert *>(
    &property_decider.get_decision_procedure());
  if(prop_conv_solver != nullptr)
    prop_conv_solver->set_all_frozen();
}

incremental_goto_checkert::resultt
concurrent_incremental_symex_checkert::operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  std::chrono::duration<double> solver_runtime(0);

  unsigned solver_calls = 0;

  const auto get_goto_function = goto_symext::get_goto_function(goto_model);

  // On first invocation, launch symex in a separate thread.
  if(!initial_equation_generated)
  {
    // Reset sync state
    sync.symex_paused = false;
    sync.symex_done = false;
    sync.solver_done = false;
    sync.stop_symex = false;
    sync.symex_exception = nullptr;

    symex_thread = std::make_unique<std::thread>(
      [&]()
      {
        try
        {
          // Start symex from entry point
          bool can_resume =
            symex.from_entry_point_of(get_goto_function, symex_symbol_table);

          {
            std::lock_guard<std::mutex> lock(sync.mtx);
            if(can_resume)
            {
              sync.symex_paused = true;
            }
            else
            {
              sync.symex_done = true;
            }
          }
          sync.cv.notify_one();

          // Loop: wait for solver, then resume symex
          while(can_resume)
          {
            {
              std::unique_lock<std::mutex> lock(sync.mtx);
              sync.cv.wait(
                lock, [this] { return sync.solver_done || sync.stop_symex; });
              sync.solver_done = false;
              if(sync.stop_symex)
                break;
            }

            can_resume = symex.resume(get_goto_function);

            {
              std::lock_guard<std::mutex> lock(sync.mtx);
              if(can_resume)
              {
                sync.symex_paused = true;
              }
              else
              {
                sync.symex_done = true;
              }
            }
            sync.cv.notify_one();
          }
        }
        catch(...)
        {
          std::lock_guard<std::mutex> lock(sync.mtx);
          sync.symex_exception = std::current_exception();
          sync.symex_done = true;
          sync.cv.notify_one();
        }
      });

    // Wait for the first batch from symex
    {
      std::unique_lock<std::mutex> lock(sync.mtx);
      sync.cv.wait(
        lock, [this] { return sync.symex_paused || sync.symex_done; });
      if(sync.symex_exception)
        std::rethrow_exception(sync.symex_exception);
    }

    // Record whether symex completed entirely
    full_equation_generated = sync.symex_done;

    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);

    initial_equation_generated = true;
  }

  // Main solving loop
  while(has_properties_to_check(properties))
  {
    if(count_properties(properties, property_statust::UNKNOWN) > 0)
    {
      const auto solver_start = std::chrono::steady_clock::now();

      if(!current_equation_converted)
      {
        postprocess_equation(symex, equation, options, ns, ui_message_handler);

        solver_runtime += prepare_property_decider_incremental(
          properties, equation, property_decider, ui_message_handler);

        current_equation_converted = true;
      }

      property_decider.add_incremental_constraint_from_goals(
        [&properties](const irep_idt &property_id)
        { return is_property_to_check(properties.at(property_id).status); });

      ++solver_calls;
      log.status()
        << "Concurrent check #" << solver_calls << ": running "
        << property_decider.get_decision_procedure().decision_procedure_text()
        << messaget::eom;

      decision_proceduret::resultt dec_result;
      // Pipeline: let symex resume during solve().
      if(!full_equation_generated)
      {
        {
          std::lock_guard<std::mutex> lock(sync.mtx);
          sync.symex_paused = false;
          sync.solver_done = true;
        }
        sync.cv.notify_one();

        dec_result = property_decider.solve();

        // Wait for symex to pause before continuing.
        {
          std::unique_lock<std::mutex> lock(sync.mtx);
          sync.cv.wait(
            lock, [this] { return sync.symex_paused || sync.symex_done; });
          if(sync.symex_exception)
          {
            if(symex_thread && symex_thread->joinable())
              symex_thread->join();
            std::rethrow_exception(sync.symex_exception);
          }
          full_equation_generated = sync.symex_done;
        }
      }
      else
      {
        dec_result = property_decider.solve();
      }

      property_decider.update_properties_status_from_goals(
        properties, result.updated_properties, dec_result, false);

      const auto solver_stop = std::chrono::steady_clock::now();
      solver_runtime +=
        std::chrono::duration<double>(solver_stop - solver_start);
      log.status() << "Runtime decision procedure: " << solver_runtime.count()
                   << "s" << messaget::eom;

      result.progress =
        dec_result == decision_proceduret::resultt::D_SATISFIABLE
          ? resultt::progresst::FOUND_FAIL
          : resultt::progresst::DONE;

      if(result.progress == resultt::progresst::FOUND_FAIL)
      {
        // Signal symex to stop and join the thread
        if(!full_equation_generated)
        {
          {
            std::lock_guard<std::mutex> lock(sync.mtx);
            sync.stop_symex = true;
            sync.solver_done = true;
          }
          sync.cv.notify_one();
          full_equation_generated = true;
        }
        if(symex_thread && symex_thread->joinable())
          symex_thread->join();
        break;
      }

      property_decider.pop_incremental_assumptions();
    }

    if(full_equation_generated)
    {
      update_status_of_unknown_properties(
        properties, result.updated_properties);

      update_status_of_not_checked_properties(
        properties, result.updated_properties);

      if(symex_thread && symex_thread->joinable())
        symex_thread->join();
      break;
    }

    // Signal symex to continue
    {
      std::lock_guard<std::mutex> lock(sync.mtx);
      sync.symex_paused = false;
      sync.solver_done = true;
    }
    sync.cv.notify_one();

    // Wait for symex to pause or finish
    {
      std::unique_lock<std::mutex> lock(sync.mtx);
      sync.cv.wait(
        lock, [this] { return sync.symex_paused || sync.symex_done; });
      if(sync.symex_exception)
      {
        if(symex_thread && symex_thread->joinable())
          symex_thread->join();
        std::rethrow_exception(sync.symex_exception);
      }
    }

    full_equation_generated = sync.symex_done;

    revert_slice(equation);

    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);

    current_equation_converted = false;
  }

  return result;
}

goto_tracet concurrent_incremental_symex_checkert::build_full_trace() const
{
  goto_tracet goto_trace;
  build_goto_trace(
    equation,
    equation.SSA_steps.end(),
    property_decider.get_decision_procedure(),
    ns,
    goto_trace);

  return goto_trace;
}

goto_tracet concurrent_incremental_symex_checkert::build_shortest_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    // NOLINTNEXTLINE(whitespace/braces)
    counterexample_beautificationt{ui_message_handler}(
      property_decider.get_boolbv_decision_procedure(), equation);
  }

  goto_tracet goto_trace;
  build_goto_trace(
    equation, property_decider.get_decision_procedure(), ns, goto_trace);

  return goto_trace;
}

goto_tracet concurrent_incremental_symex_checkert::build_trace(
  const irep_idt &property_id) const
{
  goto_tracet goto_trace;
  build_goto_trace(
    equation,
    ssa_step_matches_failing_property(property_id),
    property_decider.get_decision_procedure(),
    ns,
    goto_trace);

  return goto_trace;
}

const namespacet &concurrent_incremental_symex_checkert::get_namespace() const
{
  return ns;
}

void concurrent_incremental_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void concurrent_incremental_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}
