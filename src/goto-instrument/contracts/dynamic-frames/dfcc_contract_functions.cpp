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

#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_utils.h"

dfcc_contract_functionst::dfcc_contract_functionst(
  const symbolt &pure_contract_symbol,
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_spec_functionst &spec_functions)
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
  goto_programt &body = goto_function.body;

  for(const auto &assigns_expr : code_with_contract.assigns())
  {
    auto expr = to_lambda_expr(assigns_expr).application(lambda_parameters);
    expr.add_source_location() = assigns_expr.source_location();
    if(can_cast_expr<conditional_target_group_exprt>(expr))
    {
      encode_assignable_target_group(
        to_conditional_target_group_expr(expr), body);
    }
    else
    {
      encode_assignable_target(expr, body);
    }
  }

  body.add(goto_programt::make_end_function(spec_function_symbol.location));

  goto_model.goto_functions.update();

  inline_and_check_warnings(spec_function_id);

  PRECONDITION_WITH_DIAGNOSTICS(
    utils.has_no_loops(spec_function_id),
    "loops in assigns clause specification functions must be unwound before "
    "model instrumentation");

  goto_model.goto_functions.update();
}

void dfcc_contract_functionst::encode_assignable_target_group(
  const conditional_target_group_exprt &group,
  goto_programt &dest)
{
  const source_locationt &source_location = group.source_location();

  // clean up side effects from the condition expression if needed
  cleanert cleaner(goto_model.symbol_table, log.get_message_handler());
  exprt condition(group.condition());
  if(has_subexpr(condition, ID_side_effect))
    cleaner.clean(condition, dest, language_mode);

  // Jump target if condition is false
  auto goto_instruction = dest.add(
    goto_programt::make_incomplete_goto(not_exprt{condition}, source_location));

  for(const auto &target : group.targets())
    encode_assignable_target(target, dest);

  auto label_instruction = dest.add(goto_programt::make_skip(source_location));
  goto_instruction->complete_goto(label_instruction);
}

void dfcc_contract_functionst::encode_assignable_target(
  const exprt &target,
  goto_programt &dest)
{
  const source_locationt &source_location = target.source_location();

  if(can_cast_expr<side_effect_expr_function_callt>(target))
  {
    // A function call target `foo(params)` becomes `CALL foo(params);`
    // ```
    const auto &funcall = to_side_effect_expr_function_call(target);
    code_function_callt code_function_call(to_symbol_expr(funcall.function()));
    auto &arguments = code_function_call.arguments();
    for(auto &arg : funcall.arguments())
      arguments.emplace_back(arg);
    dest.add(
      goto_programt::make_function_call(code_function_call, source_location));
  }
  else if(is_assignable(target))
  {
    // An lvalue `target` becomes
    //` CALL __CPROVER_assignable(&target, sizeof(target), is_ptr_to_ptr);`
    const auto &size =
      size_of_expr(target.type(), namespacet(goto_model.symbol_table));

    if(!size.has_value())
    {
      throw invalid_source_file_exceptiont{
        "no definite size for lvalue assigns clause target " +
          from_expr_using_mode(ns, language_mode, target),
        target.source_location()};
    }
    // we have to build the symbol manually because it might not
    // be present in the symbol table if the user program does not already
    // use it.
    code_function_callt code_function_call(
      symbol_exprt(CPROVER_PREFIX "assignable", empty_typet()));
    auto &arguments = code_function_call.arguments();

    // ptr
    arguments.emplace_back(typecast_exprt::conditional_cast(
      address_of_exprt{target}, pointer_type(empty_typet())));

    // size
    arguments.emplace_back(size.value());

    // is_ptr_to_ptr
    arguments.emplace_back(make_boolean_expr(target.type().id() == ID_pointer));

    dest.add(
      goto_programt::make_function_call(code_function_call, source_location));
  }
  else
  {
    // any other type of target is unsupported
    throw invalid_source_file_exceptiont(
      "unsupported assigns clause target " +
        from_expr_using_mode(ns, language_mode, target),
      target.source_location());
  }
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
  goto_programt &body = goto_function.body;

  for(const auto &frees_expr : code_with_contract.frees())
  {
    auto expr = to_lambda_expr(frees_expr).application(lambda_parameters);
    expr.add_source_location() = frees_expr.source_location();
    if(can_cast_expr<conditional_target_group_exprt>(expr))
    {
      encode_freeable_target_group(
        to_conditional_target_group_expr(expr), body);
    }
    else
    {
      encode_freeable_target(expr, body);
    }
  }

  body.add(goto_programt::make_end_function(spec_function_symbol.location));

  goto_model.goto_functions.update();

  inline_and_check_warnings(spec_function_id);

  PRECONDITION_WITH_DIAGNOSTICS(
    utils.has_no_loops(spec_function_id),
    "loops in frees clause specification functions must be unwound before "
    "model instrumentation");

  goto_model.goto_functions.update();
}

void dfcc_contract_functionst::inline_and_check_warnings(
  const irep_idt &function_id)
{
  std::set<irep_idt> no_body;
  std::set<irep_idt> missing_function;
  std::set<irep_idt> recursive_call;
  std::set<irep_idt> not_enough_arguments;

  utils.inline_function(
    function_id,
    no_body,
    recursive_call,
    missing_function,
    not_enough_arguments);

  // check that the only no body / missing functions are the cprover builtins
  for(const auto &id : no_body)
  {
    INVARIANT(
      library.is_front_end_builtin(id),
      "no body for '" + id2string(id) + "' when inlining '" +
        id2string(function_id) + "'");
  }

  for(auto it : missing_function)
  {
    INVARIANT(
      library.is_front_end_builtin(it),
      "missing function '" + id2string(it) + "' when inlining '" +
        id2string(function_id) + "'");
  }

  INVARIANT(
    recursive_call.size() == 0,
    "recursive calls when inlining '" + id2string(function_id) + "'");

  INVARIANT(
    not_enough_arguments.size() == 0,
    "not enough arguments when inlining '" + id2string(function_id) + "'");
}

void dfcc_contract_functionst::encode_freeable_target_group(
  const conditional_target_group_exprt &group,
  goto_programt &dest)
{
  const source_locationt &source_location = group.source_location();

  // clean up side effects from the condition expression if needed
  cleanert cleaner(goto_model.symbol_table, log.get_message_handler());
  exprt condition(group.condition());
  if(has_subexpr(condition, ID_side_effect))
    cleaner.clean(condition, dest, language_mode);

  // Jump target if condition is false
  auto goto_instruction = dest.add(
    goto_programt::make_incomplete_goto(not_exprt{condition}, source_location));

  for(const auto &target : group.targets())
    encode_freeable_target(target, dest);

  auto label_instruction = dest.add(goto_programt::make_skip(source_location));
  goto_instruction->complete_goto(label_instruction);
}

void dfcc_contract_functionst::encode_freeable_target(
  const exprt &target,
  goto_programt &dest)
{
  const source_locationt &source_location = target.source_location();

  if(can_cast_expr<side_effect_expr_function_callt>(target))
  {
    const auto &funcall = to_side_effect_expr_function_call(target);
    if(can_cast_expr<symbol_exprt>(funcall.function()))
    {
      // for calls to user-defined functions
      // `foo(params)`
      //
      // ```
      // CALL foo(params);
      // ```
      code_function_callt code_function_call(
        to_symbol_expr(funcall.function()));
      auto &arguments = code_function_call.arguments();
      for(auto &arg : funcall.arguments())
        arguments.emplace_back(arg);
      dest.add(
        goto_programt::make_function_call(code_function_call, source_location));
    }
  }
  else if(can_cast_type<pointer_typet>(target.type()))
  {
    // A plain `target` becomes `CALL __CPROVER_freeable(target);`
    code_function_callt code_function_call(
      utils.get_function_symbol(CPROVER_PREFIX "freeable").symbol_expr());
    auto &arguments = code_function_call.arguments();
    arguments.emplace_back(target);

    dest.add(
      goto_programt::make_function_call(code_function_call, source_location));
  }
  else
  {
    // any other type of target is unsupported
    throw invalid_source_file_exceptiont(
      "unsupported frees clause target " +
        from_expr_using_mode(ns, language_mode, target),
      target.source_location());
  }
}
