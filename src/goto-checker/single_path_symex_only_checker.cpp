/*******************************************************************\

Module: Goto Checker using Single Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Single Path Symbolic Execution only

#include "single_path_symex_only_checker.h"

#include <chrono>

#include <util/ui_message.h>

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
    worklist(get_path_strategy(options.get_option("exploration-strategy"))),
    symex_runtime(0),
    unwindset(goto_model)
{
}

incremental_goto_checkert::resultt single_path_symex_only_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  initialize_worklist();

  while(!has_finished_exploration(properties))
  {
    path_storaget::patht &path = worklist->peek();

    (void)resume_path(path);

    update_properties(properties, result.updated_properties, path.equation);

    worklist->pop();
  }

  log.status() << "Runtime Symex: " << symex_runtime.count() << "s"
               << messaget::eom;

  final_update_properties(properties, result.updated_properties);

  return result;
}

void single_path_symex_only_checkert::initialize_worklist()
{
  // Put initial state into the work list
  symex_target_equationt equation(ui_message_handler);
  symex_bmct symex(
    ui_message_handler,
    goto_model.get_symbol_table(),
    equation,
    options,
    *worklist,
    guard_manager,
    unwindset);
  setup_symex(symex);

  symex.initialize_path_storage_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), symex_symbol_table);
}

bool single_path_symex_only_checkert::has_finished_exploration(
  const propertiest &properties)
{
  return worklist->empty() ||
         (!options.get_bool_option("paths-symex-explore-all") &&
          !has_properties_to_check(properties));
}

bool single_path_symex_only_checkert::resume_path(path_storaget::patht &path)
{
  const auto symex_start = std::chrono::steady_clock::now();

  symex_bmct symex(
    ui_message_handler,
    goto_model.get_symbol_table(),
    path.equation,
    options,
    *worklist,
    guard_manager,
    unwindset);
  setup_symex(symex);

  symex.resume_symex_from_saved_state(
    goto_symext::get_goto_function(goto_model),
    path.state,
    &path.equation,
    symex_symbol_table);

  const auto symex_stop = std::chrono::steady_clock::now();
  symex_runtime += std::chrono::duration<double>(symex_stop - symex_start);

  postprocess_equation(symex, path.equation, options, ns, ui_message_handler);

  equation_output(symex, path.equation);

  return is_ready_to_decide(symex, path);
}

bool single_path_symex_only_checkert::is_ready_to_decide(
  const symex_bmct &,
  const path_storaget::patht &)
{
  // we don't check anything here
  return false;
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

  if(options.get_bool_option("show-byte-ops"))
    show_byte_ops(options, ui_message_handler, ns, equation);

  if(options.get_bool_option("validate-ssa-equation"))
  {
    symex.validate(validation_modet::INVARIANT);
  }
}

void single_path_symex_only_checkert::setup_symex(symex_bmct &symex)
{
  ::setup_symex(symex, ns, options, ui_message_handler);
}

void single_path_symex_only_checkert::update_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  const symex_target_equationt &equation)
{
  if(options.get_bool_option("symex-driven-lazy-loading"))
    update_properties_from_goto_model(properties, goto_model);

  update_properties_status_from_symex_target_equation(
    properties, updated_properties, equation);
}

void single_path_symex_only_checkert::final_update_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  // For now, we assume that NOT_REACHED properties are PASS.
  update_status_of_not_checked_properties(properties, updated_properties);

  // For now, we assume that UNKNOWN properties are PASS.
  update_status_of_unknown_properties(properties, updated_properties);
}
