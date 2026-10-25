/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Periodic SAT Solver Invocation

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with periodic
/// SAT solver invocation every N symex steps

#include "periodic_incremental_symex_checker.h"

#include <util/std_expr.h>
#include <util/ui_message.h>

#include <goto-symex/slice.h>
#include <solvers/prop/prop_conv_solver.h>

#include "bmc_util.h"
#include "counterexample_beautification.h"
#include "solver_factory.h"

#include <sstream>

// --- symex_bmc_periodic_stept implementation ---

periodic_incremental_symex_checkert::symex_bmc_periodic_stept::
  symex_bmc_periodic_stept(
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
    step_interval(interval),
    last_assertion_count(0)
{
}

void periodic_incremental_symex_checkert::symex_bmc_periodic_stept::symex_step(
  const get_goto_functiont &get_goto_function,
  statet &state)
{
  symex_bmct::symex_step(get_goto_function, state);

  ++step_counter;

  if(step_counter >= step_interval)
  {
    should_pause_symex = true;
    step_counter = 0;
    last_assertion_count = target.count_assertions();
  }
  else if(step_counter >= step_interval / 4)
  {
    // Adaptive: also pause early when new assertions have appeared,
    // but only after at least 1/4 of the interval to limit overhead.
    std::size_t current = target.count_assertions();
    if(current > last_assertion_count)
    {
      should_pause_symex = true;
      step_counter = 0;
      last_assertion_count = current;
    }
  }
}

bool periodic_incremental_symex_checkert::symex_bmc_periodic_stept::
  from_entry_point_of(
    const get_goto_functiont &get_goto_function,
    symbol_tablet &new_symbol_table)
{
  state = initialize_entry_point_state(get_goto_function);

  new_symbol_table = symex_with_state(*state, get_goto_function);

  return should_pause_symex;
}

bool periodic_incremental_symex_checkert::symex_bmc_periodic_stept::resume(
  const get_goto_functiont &get_goto_function)
{
  should_pause_symex = false;

  state->symbol_table = symex_with_state(*state, get_goto_function);

  return should_pause_symex;
}

// --- periodic_incremental_symex_checkert implementation ---

periodic_incremental_symex_checkert::periodic_incremental_symex_checkert(
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
    speculative_checking_enabled(options.get_bool_option("speculative-check")),
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
periodic_incremental_symex_checkert::operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  std::chrono::duration<double> solver_runtime(0);

  unsigned solver_calls = 0;

  // we haven't got an equation yet
  if(!initial_equation_generated)
  {
    full_equation_generated = !symex.from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);

    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);

    initial_equation_generated = true;
  }

  while(has_properties_to_check(properties))
  {
    if(count_properties(properties, property_statust::UNKNOWN) > 0)
    {
      if(full_equation_generated)
      {
        // Full equation: definitive check with the main solver.
        const auto solver_start = std::chrono::steady_clock::now();

        if(!current_equation_converted)
        {
          postprocess_equation(
            symex, equation, options, ns, ui_message_handler);

          solver_runtime += prepare_property_decider_incremental(
            properties, equation, property_decider, ui_message_handler);

          current_equation_converted = true;
        }

        property_decider.add_incremental_constraint_from_goals(
          [&properties](const irep_idt &property_id)
          { return is_property_to_check(properties.at(property_id).status); });

        ++solver_calls;
        log.status()
          << "Periodic check #" << solver_calls << ": running "
          << property_decider.get_decision_procedure().decision_procedure_text()
          << messaget::eom;

        decision_proceduret::resultt dec_result = property_decider.solve();

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
          break;

        property_decider.pop_incremental_assumptions();
      }
      else if(speculative_checking_enabled)
      {
        // Speculative cone-of-influence check on partial equation.
        // Only check the most recently discovered assertion to
        // minimize overhead.
        const std::size_t current_assertions = equation.count_assertions();
        if(current_assertions > last_speculative_assertion_count)
        {
          last_speculative_assertion_count = current_assertions;

          ++solver_calls;
          log.status() << "Speculative check #" << solver_calls
                       << " on partial equation (" << equation.SSA_steps.size()
                       << " steps)" << messaget::eom;

          speculative_sat = false;
          const std::size_t snapshot_size = equation.SSA_steps.size();
          speculative_thread = std::make_unique<std::thread>(
            [this, snapshot_size]()
            {
              std::ostringstream spec_log_stream;
              stream_message_handlert spec_mh(spec_log_stream);
              spec_mh.set_verbosity(ui_message_handler.get_verbosity());

              // Find the last assertion in the snapshot.
              symex_target_equationt::SSA_stepst::const_iterator last_assert;
              bool found = false;
              std::size_t count = 0;
              for(auto it = equation.SSA_steps.begin();
                  it != equation.SSA_steps.end() && count < snapshot_size;
                  ++it, ++count)
              {
                if(it->is_assert() && !it->ignore)
                {
                  last_assert = it;
                  found = true;
                }
              }

              if(!found)
              {
                speculative_log_output = spec_log_stream.str();
                return;
              }

              auto cone = cone_of_influence(
                equation.SSA_steps, last_assert, snapshot_size);

              solver_factoryt solvers(options, ns, spec_mh, false);
              auto spec_solver = solvers.get_solver();
              auto &dp = spec_solver->decision_procedure();

              for(const auto *step : cone)
              {
                if(step->is_assignment() || step->is_constraint())
                  dp.set_to_true(step->cond_expr);
                else if(step->is_assume())
                {
                  exprt g = dp.handle(step->guard);
                  dp.set_to_true(implies_exprt(g, step->cond_expr));
                }
                else if(step->is_assert())
                {
                  exprt g = dp.handle(step->guard);
                  dp.set_to_true(implies_exprt(g, not_exprt(step->cond_expr)));
                }
              }

              if(dp() == decision_proceduret::resultt::D_SATISFIABLE)
                speculative_sat = true;

              speculative_log_output = spec_log_stream.str();
            });
        }
      }
    }

    if(full_equation_generated)
    {
      update_status_of_unknown_properties(
        properties, result.updated_properties);

      update_status_of_not_checked_properties(
        properties, result.updated_properties);

      break;
    }

    // Resume symbolic execution
    if(!full_equation_generated)
    {
      if(speculative_checking_enabled)
      {
        // Swap merge_irep so speculative thread can safely read
        // existing steps while symex appends new ones.
        merge_irept saved = equation.swap_merge_irep(merge_irept{});

        full_equation_generated =
          !symex.resume(goto_symext::get_goto_function(goto_model));

        if(speculative_thread)
        {
          speculative_thread->join();
          speculative_thread.reset();

          if(speculative_sat)
          {
            log.status() << "Speculative check found potential failure"
                         << messaget::eom;
          }

          equation.set_message_handler(ui_message_handler);
          if(!speculative_log_output.empty())
            log.debug() << speculative_log_output << messaget::eom;
        }

        equation.swap_merge_irep(std::move(saved));
      }
      else
      {
        full_equation_generated =
          !symex.resume(goto_symext::get_goto_function(goto_model));
      }

      revert_slice(equation);

      update_properties_status_from_symex_target_equation(
        properties, result.updated_properties, equation);

      current_equation_converted = false;
    }
  }

  return result;
}

goto_tracet periodic_incremental_symex_checkert::build_full_trace() const
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

goto_tracet periodic_incremental_symex_checkert::build_shortest_trace() const
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

goto_tracet periodic_incremental_symex_checkert::build_trace(
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

const namespacet &periodic_incremental_symex_checkert::get_namespace() const
{
  return ns;
}

void periodic_incremental_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void periodic_incremental_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}
