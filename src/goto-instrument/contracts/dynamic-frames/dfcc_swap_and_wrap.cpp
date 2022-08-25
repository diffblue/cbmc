/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

// TODO prune includes
#include "dfcc_swap_and_wrap.h"

#include <util/config.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/optional.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/remove_skip.h>

#include <ansi-c/c_expr.h>
#include <ansi-c/cprover_library.h>
#include <goto-instrument/contracts/cfg_info.h>
#include <goto-instrument/contracts/instrument_spec_assigns.h>
#include <goto-instrument/contracts/utils.h>
#include <linking/static_lifetime_init.h>

dfcc_swap_and_wrapt::dfcc_swap_and_wrapt(
  goto_modelt &goto_model,
  messaget &log,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument,
  dfcc_spec_functionst &spec_functions,
  dfcc_contract_handlert &contract_handler)
  : goto_model(goto_model),
    log(log),
    message_handler(log.get_message_handler()),
    utils(utils),
    library(library),
    instrument(instrument),
    spec_functions(spec_functions),
    contract_handler(contract_handler),
    ns(goto_model.symbol_table)
{
}

// static map
std::map<irep_idt, std::pair<irep_idt, dfcc_contract_modet>>
  dfcc_swap_and_wrapt::cache;

void dfcc_swap_and_wrapt::swap_and_wrap(
  const dfcc_contract_modet contract_mode,
  const irep_idt &function_id,
  const irep_idt &contract_id,
  std::set<irep_idt> &function_pointer_contracts,
  bool allow_recursive_calls)
{
  log.debug() << "->swap_and_wrap(" << function_id << "," << contract_id << ")"
              << messaget::eom;
  auto found = cache.find(function_id);
  if(found != cache.end())
  {
    auto &pair = found->second;

    // same swap already performed
    if(pair.first == contract_id && pair.second == contract_mode)
      return;

    // already swapped with something else, abort
    log.error() << " multiple attempts to swap and wrap function '"
                << function_id << "':" << messaget::eom;
    auto mode1 =
      (pair.second == dfcc_contract_modet::REPLACE) ? "REPLACE" : "CHECK";
    log.error() << "with '" << pair.first << "' in mode " << mode1
                << messaget::eom;
    auto mode2 =
      (contract_mode == dfcc_contract_modet::REPLACE) ? "REPLACE" : "CHECK)";
    log.error() << "with '" << contract_id << "' in mode " << mode2
                << messaget::eom;
    throw 0;
  }

  cache.insert({function_id, {contract_id, contract_mode}});

  switch(contract_mode)
  {
  case dfcc_contract_modet::CHECK:
  {
    check_contract(
      function_id,
      contract_id,
      function_pointer_contracts,
      allow_recursive_calls);
    break;
  }
  case dfcc_contract_modet::REPLACE:
  {
    replace_with_contract(function_id, contract_id, function_pointer_contracts);
    break;
  }
  }
  log.debug() << "<-swap_and_wrap(" << function_id << "," << contract_id << ")"
              << messaget::eom;
}

void dfcc_swap_and_wrapt::get_swapped_functions(std::set<irep_idt> &dest) const
{
  for(const auto &it : dfcc_swap_and_wrapt::cache)
  {
    dest.insert(it.first);
  }
}

/// Generates statics:
/// ```
/// static bool on_stack = false;
/// static bool checked = false;
/// ```
///
/// Generates instructions:
/// ```
/// IF on_stack GOTO replace;
/// ASSERT !checked "only a single top-level called allowed";
/// on_stack = true;
/// <add_contract_checking_instructions>;
/// checked = true;
/// on_stack = false;
/// GOTO end;
/// replace:
/// <add_contract_replacement_instructions>      // if allow_recursive_calls
/// ASSERT false, "recursive calls not allowed"; // if !allow_recursive_calls
/// end:
/// END_FUNCTION;
/// ```
void dfcc_swap_and_wrapt::check_contract(
  const irep_idt &function_id,
  const irep_idt &contract_id,
  std::set<irep_idt> &function_pointer_contracts,
  bool allow_recursive_calls)
{
  log.debug() << "->check_contract(" << function_id << "," << contract_id << ")"
              << messaget::eom;

  // all code generation needs to run on functions with unmodified signatures
  const irep_idt &wrapper_id = function_id;
  const irep_idt wrapped_id =
    id2string(wrapper_id) + "_wrapped_for_contract_checking";
  utils.wrap_function(wrapper_id, wrapped_id);

  // wrapper body
  goto_programt body;

  const auto &wrapper_symbol = utils.get_function_symbol(wrapper_id);

  auto check_started = utils
                         .create_static_symbol(
                           bool_typet(),
                           id2string(function_id),
                           "__contract_check_started",
                           wrapper_symbol.location,
                           wrapper_symbol.mode,
                           wrapper_symbol.module,
                           false_exprt())
                         .symbol_expr();

  auto check_completed = utils
                           .create_static_symbol(
                             bool_typet(),
                             id2string(function_id),
                             "__contract_check_completed",
                             wrapper_symbol.location,
                             wrapper_symbol.mode,
                             wrapper_symbol.module,
                             false_exprt())
                           .symbol_expr();

  auto check_started_goto =
    body.add(goto_programt::make_incomplete_goto(check_started));

  // At most a single top level call to the checked function in any execution

  // Recursive calls within a contract check correspond to
  // `check_started && !check_completed` and are allowed.

  // Any other call occuring with `check_completed` true is forbidden.
  source_locationt sl;
  sl.set_comment(
    "only a single top-level call to '" + id2string(function_id) +
    "' is allowed when checking contract '" + id2string(contract_id) + "'");
  body.add(goto_programt::make_assertion(not_exprt(check_completed), sl));
  body.add(goto_programt::make_assignment(check_started, true_exprt()));

  const auto write_set_symbol = utils.create_new_parameter_symbol(
    function_id,
    "__write_set_to_check",
    library.dfcc_type[dfcc_typet::CAR_SET_PTR]);

  contract_handler.add_contract_instructions(
    dfcc_contract_modet::CHECK,
    wrapper_id,
    wrapped_id,
    contract_id,
    write_set_symbol,
    body,
    function_pointer_contracts);

  body.add(goto_programt::make_assignment(check_completed, true_exprt()));

  // unconditionally Jump to the end after the check
  auto goto_end_function = body.add(goto_programt::make_incomplete_goto());

  // Jump to the replacement section if check already in progress
  auto contract_replacement_label = body.add(goto_programt::make_skip());
  check_started_goto->complete_goto(contract_replacement_label);

  // if(allow_recursive_calls)
  // {
  //   contract_handler.add_contract_instructions(
  //     dfcc_contract_modet::REPLACE,
  //     wrapper_id,
  //     wrapped_id,
  //     contract_id,
  //     write_set_symbol,
  //     body,
  //     function_pointer_contracts);
  // }
  // else
  // {
  //   source_locationt sl;
  //   sl.set_comment(
  //     "unexpected recursive call for '" + id2string(function_id) +
  //     "' when checking contract '" + id2string(contract_id) + "'");
  //   body.add(goto_programt::make_assertion(false_exprt(), sl));
  // }

  auto end_function_label = body.add(goto_programt::make_end_function());
  goto_end_function->complete_goto(end_function_label);

  // write the body to the GOTO function
  goto_model.goto_functions.function_map.at(function_id).body.swap(body);

  // extend the signature of the wrapper function with the write set parameter
  utils.add_parameter(write_set_symbol, function_id);

  utils.set_hide(wrapper_id, true);

  // instrument the wrapped function
  instrument.instrument_function(wrapped_id);

  goto_model.goto_functions.update();

  log.debug() << "<-check_contract(" << function_id << "," << contract_id << ")"
              << messaget::eom;
}

void dfcc_swap_and_wrapt::replace_with_contract(
  const irep_idt &function_id,
  const irep_idt &contract_id,
  std::set<irep_idt> &function_pointer_contracts)
{
  log.debug() << "->replace_with_contract(" << function_id << "," << contract_id
              << ")" << messaget::eom;

  const irep_idt &wrapper_id = function_id;
  const irep_idt wrapped_id =
    id2string(function_id) + "_wrapped_for_replacement_with_contract";
  utils.wrap_function(function_id, wrapped_id);

  const auto write_set_symbol = utils.create_new_parameter_symbol(
    function_id,
    "__write_set_to_check",
    library.dfcc_type[dfcc_typet::CAR_SET_PTR]);

  goto_programt body;

  contract_handler.add_contract_instructions(
    dfcc_contract_modet::REPLACE,
    wrapper_id,
    wrapped_id,
    contract_id,
    write_set_symbol,
    body,
    function_pointer_contracts);

  body.add(goto_programt::make_end_function());

  utils.set_hide(wrapper_id, true);

  // write the body to the GOTO function
  goto_model.goto_functions.function_map.at(function_id).body.swap(body);

  // extend the signature with the new write set parameter
  utils.add_parameter(write_set_symbol, function_id);
  log.debug() << "<-replace_with_contract(" << function_id << "," << contract_id
              << ")" << messaget::eom;
}
