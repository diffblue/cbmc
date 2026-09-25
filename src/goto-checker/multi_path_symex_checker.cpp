/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "multi_path_symex_checker.h"

#include <util/ui_message.h>

#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_vector.h>

#include <assembler/remove_asm.h>
#include <goto-symex/memory_model_sc.h>
#include <goto-symex/solver_hardness.h>

#include "bmc_util.h"
#include "counterexample_beautification.h"
#include "goto_symex_fault_localizer.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_only_checkert(options, ui_message_handler, goto_model),
    equation_generated(false),
    property_decider(options, ui_message_handler, equation, ns)
{
  // check for certain unsupported language features
  PRECONDITION(!has_asm(goto_model.get_goto_functions()));
  PRECONDITION(!has_function_pointers(goto_model.get_goto_functions()));
  PRECONDITION(!has_vector(goto_model.get_goto_functions()));
}

incremental_goto_checkert::resultt
multi_path_symex_checkert::operator()(propertiest &properties)
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
    generate_equation();

    output_coverage_report(
      options.get_option("symex-coverage-report"),
      goto_model,
      symex,
      ui_message_handler);

    update_properties(properties, result.updated_properties);

    // Have we got anything to check? Otherwise we return DONE.
    if(!has_properties_to_check(properties))
      return result;

    solver_runtime += prepare_property_decider(properties);

    equation_generated = true;
  }

  run_property_decider(result, properties, solver_runtime);

  return result;
}

std::chrono::duration<double>
multi_path_symex_checkert::prepare_property_decider(propertiest &properties)
{
  std::chrono::duration<double> solver_runtime = ::prepare_property_decider(
    properties, equation, property_decider, ui_message_handler);

  return solver_runtime;
}

void multi_path_symex_checkert::run_property_decider(
  incremental_goto_checkert::resultt &result,
  propertiest &properties,
  std::chrono::duration<double> solver_runtime)
{
  if(options.get_bool_option("refine-concurrency") && equation.has_threads())
  {
    // Incremental concurrency refinement: solve with progressively
    // more memory model constraints. The SAT simplifier is disabled
    // (see solver_factory.cpp) so we can add clauses between solves.
    messaget log(ui_message_handler);

    std::unique_ptr<memory_model_baset> mm = get_memory_model(options, ns);
    // prepare() was already called in postprocess_equation
    mm->prepare(equation, ui_message_handler);

    using stage = memory_model_baset::refinement_staget;
    const stage stages[] = {
      stage::READ_FROM,
      stage::PROGRAM_ORDER,
      stage::WRITE_SERIALIZATION,
      stage::FROM_READ};
    const char *stage_names[] = {
      "read-from", "program-order", "write-serialization", "from-read"};

    property_decider.add_constraint_from_goals(
      [&properties](const irep_idt &property_id)
      { return is_property_to_check(properties.at(property_id).status); });

    for(std::size_t i = 0; i <= 4; ++i)
    {
      if(i > 0)
      {
        log.statistics() << "Concurrency refinement: adding "
                         << stage_names[i - 1] << " constraints"
                         << messaget::eom;

        // Add this stage's constraints to the equation
        const auto before = equation.SSA_steps.size();
        mm->add_stage(stages[i - 1], equation);

        // Convert newly added constraint steps to the solver
        auto it = equation.SSA_steps.begin();
        std::advance(it, static_cast<std::ptrdiff_t>(before));
        for(; it != equation.SSA_steps.end(); ++it)
        {
          if(it->is_constraint())
          {
            property_decider.get_decision_procedure().set_to_true(
              it->cond_expr);
          }
        }
      }

      log.statistics() << "Concurrency refinement: solving (stage " << i
                       << "/4)" << messaget::eom;

      auto const start = std::chrono::steady_clock::now();
      decision_proceduret::resultt dec_result = property_decider.solve();
      auto const stop = std::chrono::steady_clock::now();
      solver_runtime += std::chrono::duration<double>(stop - start);

      if(dec_result == decision_proceduret::resultt::D_UNSATISFIABLE)
      {
        log.statistics() << "Concurrency refinement: UNSAT at stage " << i
                         << "/4" << messaget::eom;
        property_decider.update_properties_status_from_goals(
          properties, result.updated_properties, dec_result, true);
        break;
      }

      if(i == 4)
      {
        // All stages added, SAT is genuine
        log.statistics() << "Concurrency refinement: SAT with all constraints"
                         << messaget::eom;
        property_decider.update_properties_status_from_goals(
          properties, result.updated_properties, dec_result, true);
        result.progress =
          incremental_goto_checkert::resultt::progresst::FOUND_FAIL;
        break;
      }

      log.statistics() << "Concurrency refinement: SAT at stage " << i
                       << "/4, refining" << messaget::eom;
    }

    log.statistics() << "Runtime decision procedure: " << solver_runtime.count()
                     << "s" << messaget::eom;
  }
  else
  {
    ::run_property_decider(
      result, properties, property_decider, ui_message_handler, solver_runtime);
  }
}

goto_tracet multi_path_symex_checkert::build_full_trace() const
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

goto_tracet multi_path_symex_checkert::build_shortest_trace() const
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

goto_tracet
multi_path_symex_checkert::build_trace(const irep_idt &property_id) const
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

fault_location_infot
multi_path_symex_checkert::localize_fault(const irep_idt &property_id) const
{
  goto_symex_fault_localizert fault_localizer(
    options,
    ui_message_handler,
    equation,
    property_decider.get_decision_procedure());

  return fault_localizer(property_id);
}

void multi_path_symex_checkert::report()
{
  if(options.is_set("write-solver-stats-to"))
  {
    with_solver_hardness(
      property_decider.get_decision_procedure(),
      [](solver_hardnesst &hardness) { hardness.produce_report(); });
  }
}
