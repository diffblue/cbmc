/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution
        with Incremental Unwinding of a specified Loop

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using multi-path symbolic execution with incremental
/// unwinding of a specified loop

#include "single_loop_incremental_symex_checker.h"

#include <chrono>

#include <util/structured_data.h>

#include <goto-symex/slice.h>

#include "bmc_util.h"
#include "counterexample_beautification.h"

single_loop_incremental_symex_checkert::single_loop_incremental_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : incremental_goto_checkert(options, ui_message_handler),
    goto_model(goto_model),
    ns(goto_model.get_symbol_table(), symex_symbol_table),
    equation(ui_message_handler),
    unwindset(goto_model),
    symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      path_storage,
      guard_manager,
      unwindset,
      ui_message_handler.get_ui()),
    property_decider(options, ui_message_handler, equation, ns)
{
  setup_symex(symex, ns, options, ui_message_handler);

  // Freeze all symbols if we are using a prop_conv_solvert
  prop_conv_solvert *prop_conv_solver = dynamic_cast<prop_conv_solvert *>(
    &property_decider.get_stack_decision_procedure());
  if(prop_conv_solver != nullptr)
    prop_conv_solver->set_all_frozen();
}

void output_incremental_status(
  const propertiest &properties,
  messaget &message_hander)
{
  const auto any_failures = std::any_of(
    properties.begin(),
    properties.end(),
    [](const std::pair<irep_idt, property_infot> &property) {
      return property.second.status == property_statust::FAIL;
    });
  std::string status = any_failures ? "FAILURE" : "INCONCLUSIVE";
  structured_datat incremental_status{
    {{labelt({"incremental", "status"}),
      structured_data_entryt::data_node(json_stringt(status))}}};
  message_hander.statistics() << incremental_status;
}

incremental_goto_checkert::resultt single_loop_incremental_symex_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  std::chrono::duration<double> solver_runtime(0);

  // we haven't got an equation yet
  if(!initial_equation_generated)
  {
    full_equation_generated = !symex.from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);

    // This might add new properties such as unwinding assertions, for instance.
    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);

    initial_equation_generated = true;
  }

  while(has_properties_to_check(properties))
  {
    // There are NOT_CHECKED or UNKNOWN properties.

    if(count_properties(properties, property_statust::UNKNOWN) > 0)
    {
      // We have UNKNOWN properties, i.e. properties that we can check
      // on the current equation.

      log.status()
        << "Passing problem to "
        << property_decider.get_decision_procedure().decision_procedure_text()
        << messaget::eom;

      const auto solver_start = std::chrono::steady_clock::now();

      if(!current_equation_converted)
      {
        postprocess_equation(symex, equation, options, ns, ui_message_handler);

        log.status() << "converting SSA" << messaget::eom;
        equation.convert_without_assertions(
          property_decider.get_decision_procedure());

        property_decider.update_properties_goals_from_symex_target_equation(
          properties);

        // We convert the assertions in a new context.
        property_decider.get_stack_decision_procedure().push();
        equation.convert_assertions(
          property_decider.get_decision_procedure(), false);
        property_decider.convert_goals();

        current_equation_converted = true;
      }

      property_decider.add_constraint_from_goals(
        [&properties](const irep_idt &property_id) {
          return is_property_to_check(properties.at(property_id).status);
        });

      log.status()
        << "Running "
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

      // We've got a trace to report.
      if(result.progress == resultt::progresst::FOUND_FAIL)
        break;

      // Nothing else to do with the current set of assertions.
      // Let's pop them.
      property_decider.get_stack_decision_procedure().pop();
    }

    // Now we are finally done.
    if(full_equation_generated)
    {
      // For now, we assume that UNKNOWN properties are PASS.
      update_status_of_unknown_properties(
        properties, result.updated_properties);

      // For now, we assume that NOT_REACHED properties are PASS.
      update_status_of_not_checked_properties(
        properties, result.updated_properties);

      break;
    }

    output_incremental_status(properties, log);

    // We continue symbolic execution
    full_equation_generated =
      !symex.resume(goto_symext::get_goto_function(goto_model));
    revert_slice(equation);

    // This might add new properties such as unwinding assertions, for instance.
    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);

    current_equation_converted = false;
  }

  return result;
}

goto_tracet single_loop_incremental_symex_checkert::build_full_trace() const
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

goto_tracet single_loop_incremental_symex_checkert::build_shortest_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    // NOLINTNEXTLINE(whitespace/braces)
    counterexample_beautificationt{ui_message_handler}(
      dynamic_cast<boolbvt &>(property_decider.get_stack_decision_procedure()),
      equation);
  }

  goto_tracet goto_trace;
  build_goto_trace(
    equation, property_decider.get_decision_procedure(), ns, goto_trace);

  return goto_trace;
}

goto_tracet single_loop_incremental_symex_checkert::build_trace(
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

const namespacet &single_loop_incremental_symex_checkert::get_namespace() const
{
  return ns;
}

void single_loop_incremental_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void single_loop_incremental_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}
