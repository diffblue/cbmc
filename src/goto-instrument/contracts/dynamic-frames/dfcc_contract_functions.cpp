/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/
#include "dfcc_contract_functions.h"

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/c_expr.h>
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_contract_clauses_codegen.h"
#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_utils.h"

dfcc_contract_functionst::dfcc_contract_functionst(
  const symbolt &pure_contract_symbol,
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_spec_functionst &spec_functions,
  dfcc_contract_clauses_codegent &contract_clauses_codegen)
  : pure_contract_symbol(pure_contract_symbol),
    code_with_contract(to_code_with_contract_type(pure_contract_symbol.type)),
    spec_assigns_function_id(
      id2string(pure_contract_symbol.name) + "::assigns"),
    spec_assigns_havoc_function_id(
      id2string(pure_contract_symbol.name) + "::assigns::havoc"),
    spec_frees_function_id(id2string(pure_contract_symbol.name) + "::frees"),
    language_mode(pure_contract_symbol.mode),
    goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    spec_functions(spec_functions),
    contract_clauses_codegen(contract_clauses_codegen),
    ns(goto_model.symbol_table)
{
  gen_spec_assigns_function();

  spec_functions.generate_havoc_function(
    spec_assigns_function_id,
    spec_assigns_havoc_function_id,
    nof_assigns_targets);

  spec_functions.to_spec_assigns_function(
    spec_assigns_function_id, nof_assigns_targets);

  gen_spec_frees_function();

  spec_functions.to_spec_frees_function(
    spec_frees_function_id, nof_frees_targets);
}

const symbolt &
dfcc_contract_functionst::get_spec_assigns_function_symbol() const
{
  return ns.lookup(spec_assigns_function_id);
}

const symbolt &
dfcc_contract_functionst::get_spec_assigns_havoc_function_symbol() const
{
  return ns.lookup(spec_assigns_havoc_function_id);
}

const symbolt &dfcc_contract_functionst::get_spec_frees_function_symbol() const
{
  return ns.lookup(spec_frees_function_id);
}

const std::size_t dfcc_contract_functionst::get_nof_assigns_targets() const
{
  return nof_assigns_targets;
}

const std::size_t dfcc_contract_functionst::get_nof_frees_targets() const
{
  return nof_frees_targets;
}

void dfcc_contract_functionst::gen_spec_assigns_function()
{
  const auto &spec_function_symbol = utils.clone_and_rename_function(
    pure_contract_symbol.name, spec_assigns_function_id, empty_typet());

  const auto &spec_function_id = spec_function_symbol.name;

  auto &spec_code_type = to_code_type(spec_function_symbol.type);

  exprt::operandst lambda_parameters;

  if(code_with_contract.return_type().id() != ID_empty)
  {
    // use a dummy symbol for __CPROVER_return_value
    // which does occur in the assigns clause anyway
    lambda_parameters.push_back(
      symbol_exprt("dummy_return_value", code_with_contract.return_type()));
  }

  for(const auto &param_id : spec_code_type.parameter_identifiers())
  {
    lambda_parameters.push_back(ns.lookup(param_id).symbol_expr());
  }

  // fetch the goto_function to add instructions to
  goto_functiont &goto_function =
    goto_model.goto_functions.function_map.at(spec_function_id);

  exprt::operandst targets;

  for(const exprt &target : code_with_contract.assigns())
  {
    auto new_target = to_lambda_expr(target).application(lambda_parameters);
    new_target.add_source_location() = target.source_location();
    targets.push_back(new_target);
  }

  goto_programt &body = goto_function.body;
  contract_clauses_codegen.gen_spec_assigns_instructions(
    spec_function_symbol.mode, targets, body);
  body.add(goto_programt::make_end_function(spec_function_symbol.location));

  goto_model.goto_functions.update();
}

void dfcc_contract_functionst::gen_spec_frees_function()
{
  // fetch pure contract symbol
  const auto &code_with_contract =
    to_code_with_contract_type(pure_contract_symbol.type);

  auto &spec_function_symbol = utils.clone_and_rename_function(
    pure_contract_symbol.name, spec_frees_function_id, empty_typet());

  const auto &spec_function_id = spec_function_symbol.name;

  auto &spec_code_type = to_code_type(spec_function_symbol.type);

  exprt::operandst lambda_parameters;

  if(code_with_contract.return_type().id() != ID_empty)
  {
    // use a dummy symbol for __CPROVER_return_value
    // which does occur in the assigns clause anyway
    symbolt dummy;
    dummy.name = "dummy_return_value";
    dummy.type = code_with_contract.return_type();
    lambda_parameters.push_back(dummy.symbol_expr());
  }

  for(const auto &param_id : spec_code_type.parameter_identifiers())
  {
    lambda_parameters.push_back(ns.lookup(param_id).symbol_expr());
  }

  // fetch the goto_function to add instructions to
  goto_functiont &goto_function =
    goto_model.goto_functions.function_map.at(spec_function_id);

  exprt::operandst targets;

  for(const exprt &target : code_with_contract.frees())
  {
    auto new_target = to_lambda_expr(target).application(lambda_parameters);
    new_target.add_source_location() = target.source_location();
    targets.push_back(new_target);
  }

  goto_programt &body = goto_function.body;
  contract_clauses_codegen.gen_spec_frees_instructions(
    spec_function_symbol.mode, targets, body);
  body.add(goto_programt::make_end_function(spec_function_symbol.location));

  goto_model.goto_functions.update();
}
