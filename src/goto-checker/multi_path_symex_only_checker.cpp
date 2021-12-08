/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution Only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#include "multi_path_symex_only_checker.h"

#include <util/ui_message.h>

#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include <chrono>

#include "bmc_util.h"

multi_path_symex_only_checkert::multi_path_symex_only_checkert(
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
      unwindset)
{
  setup_symex(symex, ns, options, ui_message_handler);
}

incremental_goto_checkert::resultt multi_path_symex_only_checkert::
operator()(propertiest &properties)
{
  generate_equation();

  output_coverage_report(
    options.get_option("symex-coverage-report"),
    goto_model,
    symex,
    ui_message_handler);

  if(options.get_bool_option("show-vcc"))
  {
    show_vcc(options, ui_message_handler, equation);
  }

  if(options.get_bool_option("program-only"))
  {
    show_program(ns, equation);
  }

  if(options.get_bool_option("show-byte-ops"))
  {
    show_byte_ops(options, ui_message_handler, ns, equation);
  }

  resultt result(resultt::progresst::DONE);
  update_properties(properties, result.updated_properties);
  return result;
}

void multi_path_symex_only_checkert::generate_equation()
{
  const auto symex_start = std::chrono::steady_clock::now();

  symex.symex_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), symex_symbol_table);

  const auto symex_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> symex_runtime =
    std::chrono::duration<double>(symex_stop - symex_start);
  log.status() << "Runtime Symex: " << symex_runtime.count() << "s"
               << messaget::eom;

  postprocess_equation(symex, equation, options, ns, ui_message_handler);
}

void multi_path_symex_only_checkert::update_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  if(options.get_bool_option("symex-driven-lazy-loading"))
    update_properties_from_goto_model(properties, goto_model);

  update_properties_status_from_symex_target_equation(
    properties, updated_properties, equation);
  // Since we will not symex any further we can decide the status
  // of all properties that do not occur in the equation now.
  // The current behavior is PASS.
  update_status_of_not_checked_properties(properties, updated_properties);
}
