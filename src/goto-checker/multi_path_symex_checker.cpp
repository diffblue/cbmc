/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "multi_path_symex_checker.h"

#include <chrono>

#include <util/ui_message.h>

#include <goto-symex/solver_hardness.h>

#include "bmc_util.h"
#include "counterexample_beautification.h"
#include "goto_symex_fault_localizer.h"

#include <goto-programs/show_complexity_graph.h>

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_only_checkert(options, ui_message_handler, goto_model),
    equation_generated(false),
    property_decider(options, ui_message_handler, equation, ns)
{
}

void generate_goto_dot (const abstract_goto_modelt &goto_model,
                        const symex_bmct &symex,
                        const optionst &options,
                        ui_message_handlert &ui_message_handler,
                        const goto_symex_property_decidert &property_decider,
                        const std::string path) {
  const auto &goto_functions = goto_model.get_goto_functions();

  messaget msg(ui_message_handler);
  const namespacet ns(goto_model.get_symbol_table());
  const auto sorted = goto_functions.sorted();

  std::list<std::string> roots;
  roots.push_back (options.get_option("complexity-graph-roots"));

    const symex_coveraget &symex_coverage = symex.get_coverage();
    std::map<goto_programt::const_targett, symex_infot> instr_symex_info;
    std::map<goto_programt::const_targett, solver_infot> instr_solver_info;

    // populate instr_symex_info
    for(const auto &fun : sorted) {
      const bool has_body = fun->second.body_available();

      if (has_body) {
        const goto_programt &body = fun->second.body;
        forall_goto_program_instructions(from, body) {
          const goto_programt::const_targetst to_list = symex_coverage.coverage_to (from);
          int total_steps = 0;
          double total_duration = 0.0;
          for (goto_programt::const_targett to : to_list) {
            int to_steps = symex_coverage.num_executions(from, to);
            total_steps = total_steps + to_steps;
            total_duration = total_duration + symex_coverage.duration(from, to);
          }
          
          symex_infot info;
          info.steps = total_steps;
          info.duration = total_duration;
          
          instr_symex_info.insert ({from, info});
        }
      }
    }

    // populate instr_solver_info
    with_solver_hardness(
      property_decider.get_decision_procedure(),
      [&instr_solver_info](solver_hardnesst &solver_hardness) {
        // source: solver_hardness.cpp solver_hardnesst::produce_report
        const std::vector<std::unordered_map<solver_hardnesst::hardness_ssa_keyt, solver_hardnesst::sat_hardnesst>> &hardness_stats = solver_hardness.get_hardness_stats();
        for(std::size_t i = 0; i < hardness_stats.size(); i++) {
          const auto &ssa_step_hardness = hardness_stats[i];
          if(ssa_step_hardness.empty())
            continue;

          for(const auto &key_value_pair : ssa_step_hardness) {
            auto const &ssa = key_value_pair.first;
            auto const &hardness = key_value_pair.second;
            const goto_programt::const_targett target = ssa.pc;

            // TODO: we could also compute the number of SSA expressions associated with a GOTO, but it doesn't seem important.

            auto ensure_exists = instr_solver_info.find (target);
            if (ensure_exists == instr_solver_info.end()) {
              solver_infot solver_info;
              instr_solver_info.insert ({target, solver_info});
            }

            auto entry = instr_solver_info.find (target);
            solver_infot &solver_info = entry->second;
            solver_info.clauses += hardness.clauses;
            solver_info.literals += hardness.literals;
            solver_info.variables += hardness.variables.size();
          }
        }
      });
    if (!options.get_option ("show-complexity-graph").empty()) {
      show_complexity_graph(
        goto_model, roots, path);
    } else if (!options.get_option ("show-complexity-graph-with-symex").empty()) {
      show_complexity_graph(
        goto_model, roots, path, instr_symex_info);
    } else if (!options.get_option ("show-complexity-graph-with-solver").empty()) {
      show_complexity_graph(
        goto_model, roots, path, instr_symex_info, instr_solver_info);
    } 

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

    if (!options.get_option("show-complexity-graph").empty()) {
      generate_goto_dot(goto_model, symex, options, ui_message_handler, property_decider, options.get_option("show-complexity-graph"));
    }

    generate_equation();
    
    if (!options.get_option("show-complexity-graph-with-symex").empty()) {
      generate_goto_dot(goto_model, symex, options, ui_message_handler, property_decider, options.get_option("show-complexity-graph-with-symex"));

    }


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

    if (!options.get_option("show-complexity-graph-with-solver").empty()) {
      generate_goto_dot(goto_model, symex, options, ui_message_handler, property_decider, options.get_option("show-complexity-graph-with-solver"));

    }
  run_property_decider(result, properties, solver_runtime);
  //generate_goto_dot(goto_model, symex, options, ui_message_handler, true, property_decider);

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
  ::run_property_decider(
    result, properties, property_decider, ui_message_handler, solver_runtime);
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
      dynamic_cast<boolbvt &>(property_decider.get_stack_decision_procedure()),
      equation);
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
    property_decider.get_stack_decision_procedure());

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
