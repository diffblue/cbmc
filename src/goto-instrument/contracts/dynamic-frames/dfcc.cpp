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
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>

#include <ansi-c/ansi_c_entry_point.h>
#include <ansi-c/c_expr.h>
#include <ansi-c/c_object_factory_parameters.h>
#include <ansi-c/cprover_library.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <ansi-c/goto-conversion/link_to_library.h>
#include <goto-instrument/contracts/cfg_info.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/nondet_static.h>
#include <langapi/language.h>
#include <langapi/language_file.h>
#include <langapi/mode.h>
#include <linking/static_lifetime_init.h>

#include "dfcc_lift_memory_predicates.h"

invalid_function_contract_pair_exceptiont::
  invalid_function_contract_pair_exceptiont(
    std::string reason,
    std::string correct_format)
  : cprover_exception_baset(std::move(reason)),
    correct_format(std::move(correct_format))
{
}

std::string invalid_function_contract_pair_exceptiont::what() const
{
  std::string res;

  res += "Invalid function-contract mapping";
  res += "\nReason: " + reason;

  if(!correct_format.empty())
  {
    res += "\nFormat: " + correct_format;
  }

  return res;
}

#include <iostream>

static std::pair<irep_idt, irep_idt>
parse_function_contract_pair(const irep_idt &cli_flag)
{
  auto const correct_format_message =
    "the format for function and contract pairs is "
    "`<function_name>[/<contract_name>]`";

  std::string cli_flag_str = id2string(cli_flag);

  auto split = split_string(cli_flag_str, '/', true, false);

  if(split.size() == 1)
  {
    return std::make_pair(cli_flag, cli_flag);
  }
  else if(split.size() == 2)
  {
    auto function_name = split[0];
    if(function_name.empty())
    {
      throw invalid_function_contract_pair_exceptiont{
        "couldn't find function name before '/' in '" + cli_flag_str + "'",
        correct_format_message};
    }
    auto contract_name = split[1];
    if(contract_name.empty())
    {
      throw invalid_function_contract_pair_exceptiont{
        "couldn't find contract name after '/' in '" + cli_flag_str + "'",
        correct_format_message};
    }
    return std::make_pair(function_name, contract_name);
  }
  else
  {
    throw invalid_function_contract_pair_exceptiont{
      "couldn't parse '" + cli_flag_str + "'", correct_format_message};
  }
}

void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const std::optional<irep_idt> &to_check,
  const bool allow_recursive_calls,
  const std::set<irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const bool unwind_transformed_loops,
  const std::set<std::string> &to_exclude_from_nondet_static,
  message_handlert &message_handler)
{
  std::map<irep_idt, irep_idt> to_replace_map;
  for(const auto &cli_flag : to_replace)
    to_replace_map.insert(parse_function_contract_pair(cli_flag));

  dfcc(
    options,
    goto_model,
    harness_id,
    to_check.has_value() ? parse_function_contract_pair(to_check.value())
                         : std::optional<std::pair<irep_idt, irep_idt>>{},
    allow_recursive_calls,
    to_replace_map,
    apply_loop_contracts,
    unwind_transformed_loops,
    to_exclude_from_nondet_static,
    message_handler);
}

void dfcc(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const std::optional<std::pair<irep_idt, irep_idt>> &to_check,
  const bool allow_recursive_calls,
  const std::map<irep_idt, irep_idt> &to_replace,
  const bool apply_loop_contracts,
  const bool unwind_transformed_loops,
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
    dfcc_loop_contract_mode_from_bools(
      apply_loop_contracts, unwind_transformed_loops),
    message_handler,
    to_exclude_from_nondet_static};
}

dfcct::dfcct(
  const optionst &options,
  goto_modelt &goto_model,
  const irep_idt &harness_id,
  const std::optional<std::pair<irep_idt, irep_idt>> &to_check,
  const bool allow_recursive_calls,
  const std::map<irep_idt, irep_idt> &to_replace,
  const dfcc_loop_contract_modet loop_contract_mode,
  message_handlert &message_handler,
  const std::set<std::string> &to_exclude_from_nondet_static)
  : options(options),
    goto_model(goto_model),
    harness_id(harness_id),
    to_check(to_check),
    allow_recursive_calls(allow_recursive_calls),
    to_replace(to_replace),
    loop_contract_mode(loop_contract_mode),
    to_exclude_from_nondet_static(to_exclude_from_nondet_static),
    message_handler(message_handler),
    log(message_handler),
    library(goto_model, message_handler),
    ns(goto_model.symbol_table),
    spec_functions(goto_model, message_handler, library),
    contract_clauses_codegen(goto_model, message_handler, library),
    instrument(
      goto_model,
      message_handler,
      library,
      spec_functions,
      contract_clauses_codegen),
    memory_predicates(goto_model, library, instrument, message_handler),
    contract_handler(
      goto_model,
      message_handler,
      library,
      instrument,
      memory_predicates,
      spec_functions,
      contract_clauses_codegen),
    swap_and_wrap(
      goto_model,
      message_handler,
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
    dfcc_utilst::function_symbol_with_body_exists(goto_model, harness_id),
    "Harness function '" + id2string(harness_id) +
      "' either not found or has no body");

  if(to_check.has_value())
  {
    auto pair = to_check.value();
    PRECONDITION_WITH_DIAGNOSTICS(
      dfcc_utilst::function_symbol_with_body_exists(goto_model, pair.first),
      "Function to check '" + id2string(pair.first) +
        "' either not found or has no body");

    // triggers signature compatibility checking
    contract_handler.get_pure_contract_symbol(pair.second, pair.first);

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
      dfcc_utilst::function_symbol_exists(goto_model, pair.first),
      "Function to replace '" + id2string(pair.first) + "' not found");

    // triggers signature compatibility checking
    contract_handler.get_pure_contract_symbol(pair.second, pair.first);

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

  // disable checks on all library functions
  library.disable_checks();

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

  instrument.instrument_harness_function(
    harness_id, loop_contract_mode, function_pointer_contracts);

  other_symbols.erase(harness_id);
}

void dfcct::lift_memory_predicates()
{
  std::set<irep_idt> predicates =
    memory_predicates.lift_predicates(function_pointer_contracts);
  for(const auto &predicate : predicates)
  {
    log.debug() << "Memory predicate" << predicate << messaget::eom;
    if(other_symbols.find(predicate) != other_symbols.end())
      other_symbols.erase(predicate);
  }
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
      loop_contract_mode,
      wrapper_id,
      contract_id,
      function_pointer_contracts,
      allow_recursive_calls);

    if(other_symbols.find(wrapper_id) != other_symbols.end())
      other_symbols.erase(wrapper_id);

    // update max contract size
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
  std::set<irep_idt> swapped;
  while(!function_pointer_contracts.empty())
  {
    std::set<irep_idt> new_contracts;
    // swap-and-wrap function pointer contracts with themselves
    for(const auto &fp_contract : function_pointer_contracts)
    {
      if(swapped.find(fp_contract) != swapped.end())
        continue;

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
          dfcc_utilst::function_symbol_exists(goto_model, str),
          "Function pointer contract '" + str + "' not found.");

        // triggers signature compatibility checking
        contract_handler.get_pure_contract_symbol(str);

        log.status() << "Wrapping function pointer contract '" << fp_contract
                     << "' with itself in REPLACE mode" << messaget::eom;

        swap_and_wrap.swap_and_wrap_replace(
          fp_contract, fp_contract, new_contracts);
        swapped.insert(fp_contract);

        // remove it from the set of symbols to process
        if(other_symbols.find(fp_contract) != other_symbols.end())
          other_symbols.erase(fp_contract);
      }
    }
    // process newly discovered contracts
    function_pointer_contracts = new_contracts;
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

    instrument.instrument_function(
      function_id, loop_contract_mode, function_pointer_contracts);
  }

  goto_model.goto_functions.update();
}

void dfcct::transform_goto_model()
{
  check_transform_goto_model_preconditions();
  link_model_and_load_dfcc_library();
  lift_memory_predicates();
  instrument_harness_function();
  wrap_checked_function();
  wrap_replaced_functions();
  wrap_discovered_function_pointer_contracts();
  instrument_other_functions();

  // take the max of function of loop contracts assigns clauses
  auto assigns_clause_size = instrument.get_max_assigns_clause_size();
  if(assigns_clause_size > max_assigns_clause_size)
    max_assigns_clause_size = assigns_clause_size;

  log.status() << "Specializing cprover_contracts functions for assigns "
                  "clauses of at most "
               << max_assigns_clause_size << " targets" << messaget::eom;
  library.specialize(max_assigns_clause_size);

  library.inhibit_front_end_builtins();

  // TODO implement a means to inhibit unreachable functions (possibly via the
  // code that implements drop-unused-functions followed by
  // generate-function-bodies):
  // Traverse the call tree from the given entry point to identify
  // functions symbols that are effectively called in the model,
  // Then goes over all functions of the model and turns the bodies of all
  // functions that are not in the used function set into:
  //  ```c
  //  assert(false, "function identified as unreachable");
  //  assume(false);
  //  ```
  // That way, if the analysis mistakenly pruned some functions, assertions
  // will be violated and the analysis will fail.
  // TODO: add a command line flag to tell the instrumentation to not prune
  // a function.
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
  if(goto_model.can_produce_function(INITIALIZE_FUNCTION))
    recreate_initialize_function(goto_model, message_handler);
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
    dfcc_utilst::get_function_symbol(goto_model.symbol_table, harness_id),
    goto_model.symbol_table,
    message_handler,
    c_object_factory_parameterst(options));

  goto_model.goto_functions.update();
}
