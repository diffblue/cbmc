/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

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
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument,
  dfcc_spec_functionst &spec_functions,
  dfcc_contract_handlert &contract_handler)
  : goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
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
  auto pair = cache.insert({function_id, {contract_id, contract_mode}});
  auto inserted = pair.second;

  if(!inserted)
  {
    auto old_contract_id = pair.first->second.first;
    auto old_contract_mode = pair.first->second.second;

    // different swapp already performed, abort
    if(old_contract_id != contract_id || old_contract_mode != contract_mode)
    {
      auto mode1 = (old_contract_mode == dfcc_contract_modet::REPLACE)
                     ? "REPLACE"
                     : "CHECK";
      auto mode2 =
        (contract_mode == dfcc_contract_modet::REPLACE) ? "REPLACE" : "CHECK)";

      std::ostringstream err_msg;
      err_msg << "DFCC: multiple attempts to swap and wrap function '"
              << function_id << "':\n";
      err_msg << "- with '" << old_contract_id << "' in mode " << mode1 << "\n";
      err_msg << "- with '" << contract_id << "' in mode " << mode2 << "\n";
      throw invalid_input_exceptiont(err_msg.str());
    }
    // same swap already performed
    return;
  }

  // actually perform the translation
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
}

void dfcc_swap_and_wrapt::get_swapped_functions(std::set<irep_idt> &dest) const
{
  for(const auto &it : dfcc_swap_and_wrapt::cache)
  {
    dest.insert(it.first);
  }
}

/// \details Generates globals statics:
/// ```c
/// static bool __contract_check_in_progress = false;
/// static bool __contract_checked_once = false;
/// ```
///
/// Adds the following instructions in the wrapper function body:
/// ```c
/// IF __contract_check_in_progress GOTO replace;
/// ASSERT !__contract_checked_once "only a single top-level called allowed";
/// __contract_check_in_progress = true;
/// <contract_handler.add_contract_checking_instructions(...)>;
/// __contract_checked_once = true;
/// __contract_check_in_progress = false;
/// GOTO end;
/// replace:
/// // if allow_recursive_calls
/// <contract_handler.add_contract_replacement_instructions(...)>;
/// // if !allow_recursive_calls
/// ASSERT false, "no recursive calls";
/// ASSUME false;
/// end:
/// END_FUNCTION;
/// ```
void dfcc_swap_and_wrapt::check_contract(
  const irep_idt &function_id,
  const irep_idt &contract_id,
  std::set<irep_idt> &function_pointer_contracts,
  bool allow_recursive_calls)
{
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
                           "__contract_check_in_progress",
                           wrapper_symbol.location,
                           wrapper_symbol.mode,
                           wrapper_symbol.module,
                           false_exprt())
                         .symbol_expr();

  auto check_completed = utils
                           .create_static_symbol(
                             bool_typet(),
                             id2string(function_id),
                             "__contract_checked_once",
                             wrapper_symbol.location,
                             wrapper_symbol.mode,
                             wrapper_symbol.module,
                             false_exprt())
                           .symbol_expr();

  auto check_started_goto = body.add(goto_programt::make_incomplete_goto(
    check_started, wrapper_symbol.location));

  // At most a single top level call to the checked function in any execution

  // Recursive calls within a contract check correspond to
  // `check_started && !check_completed` and are allowed.

  // Any other call occuring with `check_completed` true is forbidden.
  source_locationt sl(wrapper_symbol.location);
  sl.set_function(wrapper_symbol.name);
  sl.set_property_class("single_top_level_call");
  sl.set_comment(
    "Only a single top-level call to function " + id2string(function_id) +
    " when checking contract " + id2string(contract_id));
  body.add(goto_programt::make_assertion(not_exprt(check_completed), sl));
  body.add(goto_programt::make_assignment(
    check_started, true_exprt(), wrapper_symbol.location));

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

  body.add(goto_programt::make_assignment(
    check_completed, true_exprt(), wrapper_symbol.location));
  body.add(goto_programt::make_assignment(
    check_started, false_exprt(), wrapper_symbol.location));

  // unconditionally Jump to the end after the check
  auto goto_end_function =
    body.add(goto_programt::make_incomplete_goto(wrapper_symbol.location));

  // Jump to the replacement section if check already in progress
  auto contract_replacement_label =
    body.add(goto_programt::make_skip(wrapper_symbol.location));
  check_started_goto->complete_goto(contract_replacement_label);

  if(allow_recursive_calls)
  {
    contract_handler.add_contract_instructions(
      dfcc_contract_modet::REPLACE,
      wrapper_id,
      wrapped_id,
      contract_id,
      write_set_symbol,
      body,
      function_pointer_contracts);
  }
  else
  {
    source_locationt sl(wrapper_symbol.location);
    sl.set_function(wrapper_symbol.name);
    sl.set_property_class("no_recursive_call");
    sl.set_comment(
      "No recursive call to function " + id2string(function_id) +
      " when checking contract " + id2string(contract_id));
    body.add(goto_programt::make_assertion(false_exprt(), sl));
    body.add(
      goto_programt::make_assumption(false_exprt(), wrapper_symbol.location));
  }

  auto end_function_label =
    body.add(goto_programt::make_end_function(wrapper_symbol.location));
  goto_end_function->complete_goto(end_function_label);

  // write the body to the GOTO function
  goto_model.goto_functions.function_map.at(function_id).body.swap(body);

  // extend the signature of the wrapper function with the write set parameter
  utils.add_parameter(write_set_symbol, function_id);

  goto_model.goto_functions.function_map.at(wrapper_id).make_hidden();

  // instrument the wrapped function
  instrument.instrument_wrapped_function(
    wrapped_id, wrapper_id, function_pointer_contracts);

  goto_model.goto_functions.update();
}

void dfcc_swap_and_wrapt::replace_with_contract(
  const irep_idt &function_id,
  const irep_idt &contract_id,
  std::set<irep_idt> &function_pointer_contracts)
{
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

  body.add(goto_programt::make_end_function(
    utils.get_function_symbol(wrapper_id).location));

  goto_model.goto_functions.function_map.at(wrapper_id).make_hidden();

  // write the body to the GOTO function
  goto_model.goto_functions.function_map.at(function_id).body.swap(body);

  // extend the signature with the new write set parameter
  utils.add_parameter(write_set_symbol, function_id);
}
