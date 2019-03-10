/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution

#include "single_path_symex_checker.h"

#include <chrono>

#include "bmc_util.h"
#include "counterexample_beautification.h"
#include "symex_bmc.h"

single_path_symex_checkert::single_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : single_path_symex_only_checkert(options, ui_message_handler, goto_model)
{
}

incremental_goto_checkert::resultt single_path_symex_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  // There might be more solutions from the previous equation.
  if(property_decider)
  {
    run_property_decider(
      result,
      properties,
      *property_decider,
      ui_message_handler,
      std::chrono::duration<double>(0),
      false);

    if(result.progress == resultt::progresst::FOUND_FAIL)
      return result;
  }

  if(!worklist->empty())
  {
    // We pop the item processed in the previous iteration.
    worklist->pop();
  }

  if(!symex_initialized)
  {
    symex_initialized = true;

    // Put initial state into the work list
    symex_target_equationt equation(ui_message_handler);
    symex_bmct symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      *worklist,
      guard_manager);
    setup_symex(symex);

    symex.initialize_path_storage_from_entry_point_of(
      goto_symext::get_goto_function(goto_model), symex_symbol_table);
  }

  while(!worklist->empty())
  {
    path_storaget::patht &resume = worklist->peek();
    symex_bmct symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      resume.equation,
      options,
      *worklist,
      guard_manager);
    setup_symex(symex);

    symex.resume_symex_from_saved_state(
      goto_symext::get_goto_function(goto_model),
      resume.state,
      &resume.equation,
      symex_symbol_table);
    postprocess_equation(
      symex, resume.equation, options, ns, ui_message_handler);

    output_coverage_report(
      options.get_option("symex-coverage-report"),
      goto_model,
      symex,
      ui_message_handler);

    if(symex.get_remaining_vccs() > 0)
    {
      update_properties_status_from_symex_target_equation(
        properties, result.updated_properties, resume.equation);

      property_decider = util_make_unique<goto_symex_property_decidert>(
        options, ui_message_handler, resume.equation, ns);

      const auto solver_runtime = prepare_property_decider(
        properties, resume.equation, *property_decider, ui_message_handler);

      run_property_decider(
        result,
        properties,
        *property_decider,
        ui_message_handler,
        solver_runtime,
        false);

      if(result.progress == resultt::progresst::FOUND_FAIL)
        return result;
    }

    worklist->pop();
  }

  // For now, we assume that NOT_REACHED properties are PASS.
  update_status_of_not_checked_properties(
    properties, result.updated_properties);

  // For now, we assume that UNKNOWN properties are PASS.
  update_status_of_unknown_properties(properties, result.updated_properties);

  // Worklist is empty: we are done.
  return result;
}

goto_tracet single_path_symex_checkert::build_full_trace() const
{
  goto_tracet goto_trace;
  build_goto_trace(
    property_decider->get_equation(),
    property_decider->get_equation().SSA_steps.end(),
    property_decider->get_solver(),
    ns,
    goto_trace);

  return goto_trace;
}

goto_tracet single_path_symex_checkert::build_shortest_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    counterexample_beautificationt()(
      dynamic_cast<boolbvt &>(property_decider->get_solver()),
      property_decider->get_equation());
  }

  goto_tracet goto_trace;
  build_goto_trace(
    property_decider->get_equation(),
    property_decider->get_solver(),
    ns,
    goto_trace);

  return goto_trace;
}

goto_tracet
single_path_symex_checkert::build_trace(const irep_idt &property_id) const
{
  goto_tracet goto_trace;
  build_goto_trace(
    property_decider->get_equation(),
    ssa_step_matches_failing_property(property_id),
    property_decider->get_solver(),
    ns,
    goto_trace);

  return goto_trace;
}

const namespacet &single_path_symex_checkert::get_namespace() const
{
  return ns;
}

void single_path_symex_checkert::output_error_witness(
  const goto_tracet &goto_trace)
{
  output_graphml(goto_trace, ns, options);
}

void single_path_symex_checkert::output_proof()
{
  // This is incorrect, but the best we can do at the moment.
  const path_storaget::patht &resume = worklist->peek();
  output_graphml(resume.equation, ns, options);
}
