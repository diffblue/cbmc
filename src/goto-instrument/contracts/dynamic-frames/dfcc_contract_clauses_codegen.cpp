/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: February 2023

\*******************************************************************/
#include "dfcc_contract_clauses_codegen.h"

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

dfcc_contract_clauses_codegent::dfcc_contract_clauses_codegent(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_spec_functionst &spec_functions)
  : goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    spec_functions(spec_functions),
    ns(goto_model.symbol_table)
{
}

void dfcc_contract_clauses_codegent::gen_spec_assigns_instructions(
  const irep_idt &language_mode,
  const exprt::operandst &assigns_clause,
  goto_programt &dest)
{
  for(const auto &expr : assigns_clause)
  {
    if(
      auto target_group =
        expr_try_dynamic_cast<conditional_target_group_exprt>(expr))
    {
      encode_assignable_target_group(language_mode, *target_group, dest);
    }
    else
    {
      encode_assignable_target(language_mode, expr, dest);
    }
  }

  // inline resulting program and check for loops
  inline_and_check_warnings(dest);
  PRECONDITION_WITH_DIAGNOSTICS(
    is_loop_free(dest, ns, log),
    "loops in assigns clause specification functions must be unwound before "
    "contracts instrumentation");
}

void dfcc_contract_clauses_codegent::gen_spec_frees_instructions(
  const irep_idt &language_mode,
  const exprt::operandst &frees_clause,
  goto_programt &dest)
{
  for(const auto &expr : frees_clause)
  {
    if(
      auto target_group =
        expr_try_dynamic_cast<conditional_target_group_exprt>(expr))
    {
      encode_freeable_target_group(language_mode, *target_group, dest);
    }
    else
    {
      encode_freeable_target(language_mode, expr, dest);
    }
  }

  // inline resulting program and check for loops
  inline_and_check_warnings(dest);
  PRECONDITION_WITH_DIAGNOSTICS(
    is_loop_free(dest, ns, log),
    "loops in assigns clause specification functions must be unwound before "
    "contracts instrumentation");
}

void dfcc_contract_clauses_codegent::encode_assignable_target_group(
  const irep_idt &language_mode,
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
    encode_assignable_target(language_mode, target, dest);

  auto label_instruction = dest.add(goto_programt::make_skip(source_location));
  goto_instruction->complete_goto(label_instruction);
}

void dfcc_contract_clauses_codegent::encode_assignable_target(
  const irep_idt &language_mode,
  const exprt &target,
  goto_programt &dest)
{
  const source_locationt &source_location = target.source_location();

  if(can_cast_expr<side_effect_expr_function_callt>(target))
  {
    // A function call target `foo(params)` becomes `CALL foo(params);`
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

void dfcc_contract_clauses_codegent::encode_freeable_target_group(
  const irep_idt &language_mode,
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
    encode_freeable_target(language_mode, target, dest);

  auto label_instruction = dest.add(goto_programt::make_skip(source_location));
  goto_instruction->complete_goto(label_instruction);
}

void dfcc_contract_clauses_codegent::encode_freeable_target(
  const irep_idt &language_mode,
  const exprt &target,
  goto_programt &dest)
{
  const source_locationt &source_location = target.source_location();

  if(can_cast_expr<side_effect_expr_function_callt>(target))
  {
    const auto &funcall = to_side_effect_expr_function_call(target);
    if(can_cast_expr<symbol_exprt>(funcall.function()))
    {
      // for calls to user-defined functions a call expression `foo(params)`
      // becomes an instruction `CALL foo(params);`
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

void dfcc_contract_clauses_codegent::inline_and_check_warnings(
  goto_programt &goto_program)
{
  std::set<irep_idt> no_body;
  std::set<irep_idt> missing_function;
  std::set<irep_idt> recursive_call;
  std::set<irep_idt> not_enough_arguments;

  utils.inline_program(
    goto_program,
    no_body,
    recursive_call,
    missing_function,
    not_enough_arguments);

  // check that the only no body / missing functions are the cprover builtins
  for(const auto &id : no_body)
  {
    INVARIANT(
      library.is_front_end_builtin(id),
      "no body for '" + id2string(id) + "' when inlining goto program");
  }

  for(auto it : missing_function)
  {
    INVARIANT(
      library.is_front_end_builtin(it),
      "missing function '" + id2string(it) + "' when inlining goto program");
  }

  INVARIANT(
    recursive_call.empty(), "recursive calls found when inlining goto program");

  INVARIANT(
    not_enough_arguments.empty(),
    "not enough arguments when inlining goto program");
}
