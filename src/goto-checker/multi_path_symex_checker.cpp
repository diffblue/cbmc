/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "multi_path_symex_checker.h"

#include <chrono>

#include "bmc_util.h"
#include "counterexample_beautification.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_only_checkert(options, ui_message_handler, goto_model),
    equation_generated(false),
    property_decider(options, ui_message_handler, equation, ns)
{
}

incremental_goto_checkert::resultt multi_path_symex_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  // When the equation has been generated, we know all the properties.
  // Have we got anything to check? Otherwise we return DONE.
  if(equation_generated && !has_properties_to_check(properties))
    return result;

  std::chrono::duration<double> solver_runtime(0);

  // we haven't got an equation yet
  if(!equation_generated)
  {
    symex.symex_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);
    postprocess_equation(symex, equation, options, ns, ui_message_handler);

    output_coverage_report(
      options.get_option("symex-coverage-report"),
      goto_model,
      symex,
      ui_message_handler);

    // This might add new properties such as unwinding assertions, for instance.
    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);
    // Since we will not symex any further we can decide the status
    // of all properties that do not occur in the equation now.
    // The current behavior is PASS.
    update_status_of_not_checked_properties(
      properties, result.updated_properties);

    // Have we got anything to check? Otherwise we return DONE.
    if(!has_properties_to_check(properties))
      return result;

    log.status() << "Passing problem to "
                 << property_decider.get_solver().decision_procedure_text()
                 << messaget::eom;

    const auto solver_start = std::chrono::steady_clock::now();

    convert_symex_target_equation(
      equation, property_decider.get_solver(), ui_message_handler);
    property_decider.update_properties_goals_from_symex_target_equation(
      properties);
    property_decider.convert_goals();
    property_decider.freeze_goal_variables();

    const auto solver_stop = std::chrono::steady_clock::now();
    solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);

    log.status() << "Running "
                 << property_decider.get_solver().decision_procedure_text()
                 << messaget::eom;
    equation_generated = true;
  }

  const auto solver_start = std::chrono::steady_clock::now();

  property_decider.add_constraint_from_goals(
    [&properties](const irep_idt &property_id) {
      return is_property_to_check(properties.at(property_id).status);
    });

  decision_proceduret::resultt dec_result = property_decider.solve();

  property_decider.update_properties_status_from_goals(
    properties, result.updated_properties, dec_result);

  const auto solver_stop = std::chrono::steady_clock::now();
  solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);
  log.status() << "Runtime decision procedure: " << solver_runtime.count()
               << "s" << messaget::eom;

  result.progress = dec_result == decision_proceduret::resultt::D_SATISFIABLE
                      ? resultt::progresst::FOUND_FAIL
                      : resultt::progresst::DONE;
  return result;
}

goto_tracet multi_path_symex_checkert::build_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    counterexample_beautificationt()(
      dynamic_cast<boolbvt &>(property_decider.get_solver()), equation);
  }
  goto_tracet goto_trace;
  ::build_error_trace(
    goto_trace,
    ns,
    equation,
    property_decider.get_solver(),
    ui_message_handler);
  return goto_trace;
}

const namespacet &multi_path_symex_checkert::get_namespace() const
{
  return ns;
}

void multi_path_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void multi_path_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}
