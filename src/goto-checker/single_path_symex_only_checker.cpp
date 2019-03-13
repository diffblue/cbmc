/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution only

#include "single_path_symex_only_checker.h"

#include <chrono>

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/path_storage.h>
#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include "bmc_util.h"
#include "symex_bmc.h"

single_path_symex_only_checkert::single_path_symex_only_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : incremental_goto_checkert(options, ui_message_handler),
    goto_model(goto_model),
    ns(goto_model.get_symbol_table(), symex_symbol_table),
    worklist(get_path_strategy(options.get_option("exploration-strategy")))
{
}

incremental_goto_checkert::resultt single_path_symex_only_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  {
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

  while(!worklist->empty() &&
        (options.get_bool_option("paths-symex-explore-all") ||
         has_properties_to_check(properties)))
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

    equation_output(symex, resume.equation);

    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, resume.equation);

    worklist->pop();
  }

  // For now, we assume that NOT_REACHED properties are PASS.
  update_status_of_not_checked_properties(
    properties, result.updated_properties);
  return result;
}

void single_path_symex_only_checkert::equation_output(
  const symex_bmct &symex,
  const symex_target_equationt &equation)
{
  output_coverage_report(
    options.get_option("symex-coverage-report"),
    goto_model,
    symex,
    ui_message_handler);

  if(options.get_bool_option("show-vcc"))
    show_vcc(options, ui_message_handler, equation);

  if(options.get_bool_option("program-only"))
    show_program(ns, equation);

  if(options.get_bool_option("validate-ssa-equation"))
  {
    symex.validate(validation_modet::INVARIANT);
  }
}

void single_path_symex_only_checkert::setup_symex(symex_bmct &symex)
{
  ::setup_symex(symex, ns, options, ui_message_handler);
}
