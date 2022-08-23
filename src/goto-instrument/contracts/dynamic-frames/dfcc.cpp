/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

#include "dfcc.h"

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
#include <util/prefix.h>
#include <util/std_expr.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>

#include <ansi-c/ansi_c_entry_point.h>
#include <ansi-c/c_expr.h>
#include <ansi-c/c_object_factory_parameters.h>
#include <ansi-c/cprover_library.h>
#include <goto-instrument/contracts/cfg_info.h>
#include <goto-instrument/contracts/instrument_spec_assigns.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/nondet_static.h>
#include <langapi/language.h>
#include <langapi/language_file.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>

void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const optionalt<irep_idt> &to_check,
  const bool allow_recursive_calls,
  const std::set<irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &to_exclude_from_nondet_static,
  message_handlert &message_handler)
{
  std::map<irep_idt, irep_idt> to_replace_map;
  for(const auto &function_id : to_replace)
    to_replace_map.insert({function_id, function_id});

  dfcc(
    options,
    goto_model,
    harness_id,
    to_check.has_value()
      ? optionalt<std::pair<irep_idt, irep_idt>>(
          std::pair<irep_idt, irep_idt>(to_check.value(), to_check.value()))
      : optionalt<std::pair<irep_idt, irep_idt>>{},
    allow_recursive_calls,
    to_replace_map,
    apply_loop_contracts,
    to_exclude_from_nondet_static,
    message_handler);
}

void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const optionalt<std::pair<irep_idt, irep_idt>> &to_check,
  const bool allow_recursive_calls,
  const std::map<irep_idt, irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const std::set<std::string> &to_exclude_from_nondet_static,
  message_handlert &message_handler)
{
  dfcct{
    options,
    goto_model,
    harness_id,
    to_check,
    allow_recursive_calls,
    to_replace,
    apply_loop_contracts,
    message_handler,
    to_exclude_from_nondet_static};
}

dfcct::dfcct(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const optionalt<std::pair<irep_idt, irep_idt>> &to_check,
  const bool allow_recursive_calls,
  const std::map<irep_idt, irep_idt> &to_replace,
  const bool apply_loop_contracts,
  message_handlert &message_handler,
  const std::set<std::string> &to_exclude_from_nondet_static)
  : options(options),
    goto_model(goto_model),
    harness_id(harness_id),
    to_check(to_check),
    allow_recursive_calls(allow_recursive_calls),
    to_replace(to_replace),
    apply_loop_contracts(apply_loop_contracts),
    to_exclude_from_nondet_static(to_exclude_from_nondet_static),
    message_handler(message_handler),
    log(message_handler),
    utils(goto_model, message_handler),
    library(goto_model, utils, message_handler),
    ns(goto_model.symbol_table),
    instrument(goto_model, message_handler, utils, library),
    spec_functions(goto_model, message_handler, utils, library, instrument),
    contract_handler(
      goto_model,
      message_handler,
      utils,
      library,
      instrument,
      spec_functions),
    swap_and_wrap(
      goto_model,
      message_handler,
      utils,
      library,
      instrument,
      spec_functions,
      contract_handler),
    max_assigns_clause_size(0)
{
  transform_goto_model();
}

void dfcct::check_transform_goto_model_preconditions()
{
  // check that harness function exists
  PRECONDITION_WITH_DIAGNOSTICS(
    utils.function_symbol_with_body_exists(harness_id),
    "Harness function '" + id2string(harness_id) +
      "' either not found or has no body");

  if(to_check.has_value())
  {
    auto pair = to_check.value();
    PRECONDITION_WITH_DIAGNOSTICS(
      utils.function_symbol_with_body_exists(pair.first),
      "Function to check '" + id2string(pair.first) +
        "' either not found or has no body");

    // triggers signature compatibility checking
    contract_handler.get_pure_contract_symbol(pair.second);

    PRECONDITION_WITH_DIAGNOSTICS(
      pair.first != harness_id,
      "Function '" + id2string(pair.first) +
        "' cannot be both be checked against a contract and be the harness");

    PRECONDITION_WITH_DIAGNOSTICS(
      pair.second != harness_id,
      "Function '" + id2string(pair.first) +
        "' cannot be both the contract to check and be the harness");

    PRECONDITION_WITH_DIAGNOSTICS(
      to_replace.find(pair.first) == to_replace.end(),
      "Function '" + id2string(pair.first) +
        "' cannot be both checked against contract and replaced by a contract");

    PRECONDITION_WITH_DIAGNOSTICS(
      !instrument.do_not_instrument(pair.first),
      "CPROVER function or builtin '" + id2string(pair.first) +
        "' cannot be checked against a contract");
  }

  for(const auto &pair : to_replace)
  {
    // for functions to replace with contracts we don't require the replaced
    // function to have a body because only the contract is actually used
    PRECONDITION_WITH_DIAGNOSTICS(
      utils.function_symbol_exists(pair.first),
      "Function to replace '" + id2string(pair.first) + "' not found");

    // triggers signature compatibility checking
    contract_handler.get_pure_contract_symbol(pair.second);

    PRECONDITION_WITH_DIAGNOSTICS(
      pair.first != harness_id,
      "Function '" + id2string(pair.first) +
        "' cannot both be replaced with a contract and be the harness");

    PRECONDITION_WITH_DIAGNOSTICS(
      pair.second != harness_id,
      "Function '" + id2string(pair.first) +
        "' cannot both be the contract to use for replacement and be the "
        "harness");
  }
}

void dfcct::partition_function_symbols(
  std::set<irep_idt> &contract_symbols,
  std::set<irep_idt> &other_symbols)
{
  // collect contract and other symbols
  for(auto &entry : goto_model.symbol_table)
  {
    const symbolt &symbol = entry.second;

    // not a function symbol
    if(symbol.type.id() != ID_code)
      continue;

    // is it a pure contract ?
    const irep_idt &sym_name = symbol.name;
    if(symbol.is_property && has_prefix(id2string(sym_name), "contract::"))
    {
      contract_symbols.insert(sym_name);
    }
    else
    {
      // it is not a contract
      other_symbols.insert(sym_name);
    }
  }
}

void dfcct::link_model_and_load_dfcc_library()
{
  // load the cprover library to make sure the model is complete
  log.status() << "Loading CPROVER C library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);

  // this  must be done before loading the dfcc lib
  partition_function_symbols(pure_contract_symbols, other_symbols);

  // load the dfcc library before instrumentation starts
  library.load(other_symbols);

  // add C prover lib again to fetch any dependencies of the dfcc functions
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);
}

void dfcct::instrument_harness_function()
{
  // instrument the harness function
  // load the cprover library to make sure the model is complete
  log.status() << "Instrumenting harness function '" << harness_id << "'"
               << messaget::eom;
  instrument.instrument_harness_function(harness_id);

  other_symbols.erase(harness_id);
}

void dfcct::wrap_checked_function()
{
  // swap-and-wrap checked functions with contracts
  if(to_check.has_value())
  {
    const auto &pair = to_check.value();
    const auto &wrapper_id = pair.first;
    const auto &contract_id = pair.second;
    log.status() << "Wrapping '" << wrapper_id << "' with contract '"
                 << contract_id << "' in CHECK mode" << messaget::eom;

    swap_and_wrap.swap_and_wrap_check(
      wrapper_id,
      contract_id,
      function_pointer_contracts,
      allow_recursive_calls);

    if(other_symbols.find(wrapper_id) != other_symbols.end())
      other_symbols.erase(wrapper_id);

    // upate max contract size
    const std::size_t assigns_clause_size =
      contract_handler.get_assigns_clause_size(contract_id);
    if(assigns_clause_size > max_assigns_clause_size)
      max_assigns_clause_size = assigns_clause_size;
  }
}

void dfcct::wrap_replaced_functions()
{
  // swap-and-wrap replaced functions with contracts
  for(const auto &pair : to_replace)
  {
    const auto &wrapper_id = pair.first;
    const auto &contract_id = pair.second;
    log.status() << "Wrapping '" << wrapper_id << "' with contract '"
                 << contract_id << "' in REPLACE mode" << messaget::eom;
    swap_and_wrap.swap_and_wrap_replace(
      wrapper_id, contract_id, function_pointer_contracts);

    if(other_symbols.find(wrapper_id) != other_symbols.end())
      other_symbols.erase(wrapper_id);
  }
}

void dfcct::wrap_discovered_function_pointer_contracts()
{
  // swap-and-wrap function pointer contracts with themselves
  for(const auto &fp_contract : function_pointer_contracts)
  {
    log.status() << "Discovered function pointer contract '" << fp_contract
                 << "'" << messaget::eom;

    // contracts for function pointers must be replaced with themselves
    // so we need to check that:
    // - the symbol exists as a function symbol
    // - the symbol exists as a pure contract symbol
    // - the function symbol is not already swapped for contract checking
    // - the function symbol is not already swapped with another contract for
    // replacement

    const auto str = id2string(fp_contract);

    // Is it already swapped with another function for contract checking ?
    PRECONDITION_WITH_DIAGNOSTICS(
      !to_check.has_value() || to_check.value().first != str,
      "Function '" + str +
        "' used as contract for function pointer cannot be itself the object "
        "of a contract check.");

    // Is it already swapped with another function for contract checking ?
    auto found = to_replace.find(str);
    if(found != to_replace.end())
    {
      PRECONDITION_WITH_DIAGNOSTICS(
        found->first == found->second,
        "Function '" + str +
          "' used as contract for function pointer already the object of a "
          "contract replacement with '" +
          id2string(found->second) + "'");
      log.status() << "Function pointer contract '" << fp_contract
                   << "' already wrapped with itself in REPLACE mode"
                   << messaget::eom;
    }
    else
    {
      // we need to swap it with itself
      PRECONDITION_WITH_DIAGNOSTICS(
        utils.function_symbol_exists(str),
        "Function pointer contract '" + str + "' not found.");

      // triggers signature compatibility checking
      contract_handler.get_pure_contract_symbol(str);

      log.status() << "Wrapping function pointer contract '" << fp_contract
                   << "' with itself in REPLACE mode" << messaget::eom;

      swap_and_wrap.swap_and_wrap_replace(
        fp_contract, fp_contract, function_pointer_contracts);
      // remove it from the set of symbols to process
      if(other_symbols.find(fp_contract) != other_symbols.end())
        other_symbols.erase(fp_contract);
    }
  }
}

void dfcct::instrument_other_functions()
{
  // instrument all other remaining functions
  for(const auto &function_id : other_symbols)
  {
    // Don't instrument CPROVER and internal functions
    if(instrument.do_not_instrument(function_id))
    {
      continue;
    }

    log.status() << "Instrumenting '" << function_id << "'" << messaget::eom;

    instrument.instrument_function(function_id);
  }

  goto_model.goto_functions.update();

  if(to_check.has_value())
  {
    log.status() << "Specializing cprover_contracts functions for assigns "
                    "clauses of at most "
                 << max_assigns_clause_size << " targets" << messaget::eom;
    library.specialize(max_assigns_clause_size);
  }
}

void dfcct::transform_goto_model()
{
  check_transform_goto_model_preconditions();
  link_model_and_load_dfcc_library();
  instrument_harness_function();
  wrap_checked_function();
  wrap_replaced_functions();
  wrap_discovered_function_pointer_contracts();
  instrument_other_functions();
  library.inhibit_front_end_builtins();

  // TODO implement and use utils.inhibit_unreachable_functions(harness);
  goto_model.goto_functions.update();

  remove_skip(goto_model);
  goto_model.goto_functions.update();

  log.status() << "Removing unused functions" << messaget::eom;

  // This can prune too many functions if function pointers have not been
  // yet been removed or if the entry point is not defined.
  // Another solution would be to rewrite the bodies of functions that seem to
  // be unreachable into assert(false);assume(false)
  remove_unused_functions(goto_model, message_handler);
  goto_model.goto_functions.update();

  reinitialize_model();
}

void dfcct::reinitialize_model()
{
  // collect set of functions which are now instrumented
  std::set<irep_idt> instrumented_functions;
  instrument.get_instrumented_functions(instrumented_functions);
  swap_and_wrap.get_swapped_functions(instrumented_functions);

  log.status() << "Updating init function" << messaget::eom;
  utils.create_initialize_function();
  goto_model.goto_functions.update();
  nondet_static(goto_model, to_exclude_from_nondet_static);

  // Initialize the map of instrumented functions by adding extra instructions
  // to the harness function
  auto &init_function = goto_model.goto_functions.function_map[harness_id];
  auto &body = init_function.body;
  auto begin = body.instructions.begin();
  goto_programt payload;
  library.add_instrumented_functions_map_init_instructions(
    instrumented_functions, begin->source_location(), payload);
  body.destructive_insert(begin, payload);

  // Define harness as the entry point, overriding any preexisting one.
  log.status() << "Setting entry point to " << harness_id << messaget::eom;
  // remove the CPROVER start function
  goto_model.symbol_table.erase(
    goto_model.symbol_table.symbols.find(goto_functionst::entry_point()));
  // regenerate the CPROVER start function
  generate_ansi_c_start_function(
    utils.get_function_symbol(harness_id),
    goto_model.symbol_table,
    message_handler,
    c_object_factory_parameterst(options));

  goto_model.goto_functions.update();
}
