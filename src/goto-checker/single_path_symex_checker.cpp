/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution

#include "single_path_symex_checker.h"

#include <util/ui_message.h>

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
      result, properties, *property_decider, std::chrono::duration<double>(0));

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

    initialize_worklist();
  }

  while(!has_finished_exploration(properties))
  {
    path_storaget::patht &path = worklist->peek();
    const bool ready_to_decide = resume_path(path);

    if(ready_to_decide)
    {
      update_properties(properties, result.updated_properties, path.equation);

      property_decider = util_make_unique<goto_symex_property_decidert>(
        options, ui_message_handler, path.equation, ns);

      const auto solver_runtime =
        prepare_property_decider(properties, path.equation, *property_decider);

      run_property_decider(
        result, properties, *property_decider, solver_runtime);

      if(result.progress == resultt::progresst::FOUND_FAIL)
        return result;
    }

    // leave the last worklist item in place for the benefit of output_proof
    if(worklist->size() == 1)
      break;

    worklist->pop();
  }

  log.status() << "Runtime Symex: " << symex_runtime.count() << "s"
               << messaget::eom;

  final_update_properties(properties, result.updated_properties);

  // Worklist just has the last element left: we are done.
  return result;
}

bool single_path_symex_checkert::is_ready_to_decide(
  const symex_bmct &symex,
  const path_storaget::patht &)
{
  return symex.get_remaining_vccs() > 0;
}

std::chrono::duration<double>
single_path_symex_checkert::prepare_property_decider(
  propertiest &properties,
  symex_target_equationt &equation,
  goto_symex_property_decidert &property_decider)
{
  std::chrono::duration<double> solver_runtime = ::prepare_property_decider(
    properties, equation, property_decider, ui_message_handler);

  return solver_runtime;
}

void single_path_symex_checkert::run_property_decider(
  incremental_goto_checkert::resultt &result,
  propertiest &properties,
  goto_symex_property_decidert &property_decider,
  std::chrono::duration<double> solver_runtime)
{
  ::run_property_decider(
    result,
    properties,
    property_decider,
    ui_message_handler,
    solver_runtime,
    false);
}

goto_tracet single_path_symex_checkert::build_full_trace() const
{
  goto_tracet goto_trace;
  build_goto_trace(
    property_decider->get_equation(),
    property_decider->get_equation().SSA_steps.end(),
    property_decider->get_decision_procedure(),
    ns,
    goto_trace);

  return goto_trace;
}

goto_tracet single_path_symex_checkert::build_shortest_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    // NOLINTNEXTLINE(whitespace/braces)
    counterexample_beautificationt{ui_message_handler}(
      dynamic_cast<boolbvt &>(property_decider->get_stack_decision_procedure()),
      property_decider->get_equation());
  }

  goto_tracet goto_trace;
  build_goto_trace(
    property_decider->get_equation(),
    property_decider->get_decision_procedure(),
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
    property_decider->get_decision_procedure(),
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
  // operator()(propertiest &properties) leaves in place the last worklist item
  // just for this purpose.
  const path_storaget::patht &resume = worklist->peek();
  output_graphml(resume.equation, ns, options);
}
