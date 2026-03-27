/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution Only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#include "multi_path_symex_only_checker.h"

#include <util/memory_info.h>
#include <util/ui_message.h>

#include <goto-symex/shadow_memory.h>
#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include "bmc_util.h"

#include <algorithm>
#include <fstream>

multi_path_symex_only_checkert::multi_path_symex_only_checkert(
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
      unwindset)
{
  unwindset.parse_unwind(options.get_option("unwind"));
  unwindset.parse_unwindset(
    options.get_list_option("unwindset"), goto_model, ui_message_handler);
}

incremental_goto_checkert::resultt
multi_path_symex_only_checkert::operator()(propertiest &properties)
{
  generate_equation();

  output_coverage_report(
    options.get_option("symex-coverage-report"),
    goto_model,
    symex,
    ui_message_handler);

  // Write callgrind-format symex profile if requested
  {
    const std::string callgrind_file = options.get_option("symex-callgrind");
    if(!callgrind_file.empty())
    {
      std::ofstream out(callgrind_file);
      if(out)
      {
        symex.write_callgrind(out);
        log.status() << "Symex callgrind data written to " << callgrind_file
                     << messaget::eom;
      }
    }
  }

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
  // Gather fields for shadow memory instrumentation
  const auto fields =
    shadow_memoryt::gather_field_declarations(goto_model, ui_message_handler);

  const auto symex_start = std::chrono::steady_clock::now();

  symex_symbol_table = symex.symex_from_entry_point_of(
    goto_symext::get_goto_function(goto_model), fields);

  const auto symex_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> symex_runtime =
    std::chrono::duration<double>(symex_stop - symex_start);
  log.statistics() << "Runtime Symex: " << symex_runtime.count() << "s"
                   << messaget::eom;

  // Report per-function symex step counts (top contributors)
  const auto &step_counts = symex.get_function_step_counts();
  if(!step_counts.empty())
  {
    // Sort by step count descending
    std::vector<std::pair<irep_idt, std::size_t>> sorted(
      step_counts.begin(), step_counts.end());
    std::sort(
      sorted.begin(),
      sorted.end(),
      [](const auto &a, const auto &b) { return a.second > b.second; });

    std::size_t total = 0;
    for(const auto &entry : sorted)
      total += entry.second;

    log.statistics() << "Symex steps: " << total << " total" << messaget::eom;

    const std::size_t max_entries = 10;
    for(std::size_t i = 0; i < std::min(max_entries, sorted.size()); ++i)
    {
      log.statistics() << "  " << sorted[i].first << ": " << sorted[i].second
                       << " steps ("
                       << (100 * sorted[i].second + total / 2) / total << "%)"
                       << messaget::eom;
    }
  }

  log.statistics() << "Peak memory: " << peak_memory_bytes() / (1024 * 1024)
                   << " MB" << messaget::eom;

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
