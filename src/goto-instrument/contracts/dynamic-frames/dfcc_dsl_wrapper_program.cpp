/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_dsl_wrapper_program.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/c_expr.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_dsl_contract_functions.h"
#include "dfcc_instrument.h"
#include "dfcc_is_freeable.h"
#include "dfcc_is_fresh.h"
#include "dfcc_library.h"
#include "dfcc_utils.h"

dfcc_dsl_wrapper_programt::dfcc_dsl_wrapper_programt(
  const dfcc_contract_modet contract_mode,
  const symbolt &wrapper_symbol,
  const symbolt &wrapped_symbol,
  const dfcc_dsl_contract_functionst &contract_functions,
  const symbolt &caller_write_set_symbol,
  goto_modelt &goto_model,
  messaget &log,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument)
  : contract_mode(contract_mode),
    wrapper_symbol(wrapper_symbol),
    wrapped_symbol(wrapped_symbol),
    contract_functions(contract_functions),
    contract_symbol(contract_functions.pure_contract_symbol),
    contract_code_type(to_code_with_contract_type(contract_symbol.type)),
    caller_write_set_symbol(caller_write_set_symbol),
    return_value_symbol_opt(nullptr),
    contract_write_set_symbol_opt(nullptr),
    addr_of_contract_write_set_symbol_opt(nullptr),
    requires_write_set_symbol_opt(nullptr),
    addr_of_requires_write_set_symbol_opt(nullptr),
    ensures_write_set_symbol_opt(nullptr),
    addr_of_ensures_write_set_symbol_opt(nullptr),
    function_pointer_contracts(),
    goto_model(goto_model),
    log(log),
    utils(utils),
    library(library),
    instrument(instrument),
    ns(goto_model.symbol_table),
    converter(goto_model.symbol_table, log.get_message_handler())
{
  // generate a return value symbol (needed to instanciate all contract lambdas)
  if(contract_code_type.return_type().id() != ID_empty)
  {
    return_value_symbol_opt = &utils.create_symbol(
      contract_code_type.return_type(),
      id2string(wrapper_symbol.name),
      "__contract_return_value",
      wrapper_symbol.location,
      wrapper_symbol.module,
      wrapper_symbol.mode,
      false);
  }

  // generate a contract write set
  contract_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET],
    id2string(wrapper_symbol.name),
    "__contract_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // generate a contract write set pointer
  addr_of_contract_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
    id2string(wrapper_symbol.name),
    "__address_of_contract_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // generate local write set symbol to check for side effects in pre and post
  // conditions
  requires_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET],
    id2string(wrapper_symbol.name),
    "__requires_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // generate local write set symbol to check for side effects in pre and post
  // conditions
  addr_of_requires_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
    id2string(wrapper_symbol.name),
    "__address_of_requires_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // generate local write set symbol to check for side effects in pre and post
  // conditions
  ensures_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET],
    id2string(wrapper_symbol.name),
    "__ensures_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // generate local write set symbol to check for side effects in pre and post
  // conditions
  addr_of_ensures_write_set_symbol_opt = &utils.create_symbol(
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
    id2string(wrapper_symbol.name),
    "__address_of_ensures_write_set",
    wrapper_symbol.location,
    wrapper_symbol.mode,
    wrapper_symbol.module,
    false);

  // build contract_lambda_parameters
  if(contract_code_type.return_type().id() != ID_empty)
  {
    contract_lambda_parameters.push_back(
      return_value_symbol_opt->symbol_expr());
  }

  for(const auto &param_id :
      to_code_type(wrapper_symbol.type).parameter_identifiers())
  {
    contract_lambda_parameters.push_back(ns.lookup(param_id).symbol_expr());
  }

  // encode all contract clauses
  encode_requires_write_set();
  encode_requires_clauses();
  encode_requires_contract_clauses();
  encode_contract_write_set();
  encode_function_call();
  encode_ensures_write_set();
  encode_ensures_clauses();
  encode_ensures_contract_clauses();
}

void dfcc_dsl_wrapper_programt::add_to_dest(
  goto_programt &dest,
  std::set<irep_idt> &dest_fp_contracts)
{
  add_to_dest(dest);
  dest_fp_contracts.insert(
    function_pointer_contracts.begin(), function_pointer_contracts.end());
}

void dfcc_dsl_wrapper_programt::add_to_dest(goto_programt &dest)
{
  // add code to dest in the right order
  dest.destructive_append(preamble);
  dest.destructive_append(preconditions);
  dest.destructive_append(history);
  dest.destructive_append(write_set_checks);
  dest.destructive_append(function_call);
  dest.destructive_append(link_caller_write_set);
  dest.destructive_append(link_deallocated);
  dest.destructive_append(postconditions);
  dest.destructive_append(postamble);
}

void dfcc_dsl_wrapper_programt::encode_requires_write_set()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_requires_write_set()"
              << messaget::eom;

  PRECONDITION(requires_write_set_symbol_opt);
  PRECONDITION(addr_of_requires_write_set_symbol_opt);

  // call set_create(
  //   requires_write_set,
  //   assigns_size = 0,
  //   frees_size = 0,
  //   replacement_mode = false,
  //   assume_requires_ctx = contract_mode == check,
  //   assert_requires_ctx = contract_mode != check,
  //   assume_ensures_ctx = false,
  //   assert_ensures_ctx = false,
  // )
  const auto write_set = requires_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(write_set));

  const auto address_of_write_set =
    addr_of_requires_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(address_of_write_set));
  preamble.add(goto_programt::make_assignment(
    address_of_write_set, address_of_exprt(write_set)));

  auto function_symbol =
    library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_CREATE).symbol_expr();
  code_function_callt call(function_symbol);
  auto &arguments = call.arguments();

  // write set
  arguments.emplace_back(address_of_write_set);

  // max assigns clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // max frees clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // replacement mode
  arguments.emplace_back((exprt)false_exprt());

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    // assume_requires_ctx
    arguments.emplace_back((exprt)true_exprt());

    // assert_requires_ctx
    arguments.emplace_back((exprt)false_exprt());
  }
  else
  {
    // assume_requires_ctx
    arguments.emplace_back((exprt)false_exprt());

    // assert_requires_ctx mode
    arguments.emplace_back((exprt)true_exprt());
  }

  // assume_ensures_ctx mode
  arguments.emplace_back((exprt)false_exprt());

  // assert_ensures_ctx mode
  arguments.emplace_back((exprt)false_exprt());

  preamble.add(goto_programt::make_function_call(call));

  // check for absence of allocation/deallocation in requires clauses
  // ```
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc =
  // check_empty_alloc_dealloct(write_set, lhs, sizeof(lhs));
  // ASSERT(__check_no_alloc);
  // DEAD __check_no_alloc: bool;
  // ```
  auto check_var = get_fresh_aux_symbol(
                     bool_typet(),
                     id2string(wrapper_symbol.name),
                     "__no_alloc_dealloc_in_requires",
                     source_locationt{}, // TODO add property class and comment
                     wrapper_symbol.mode,
                     goto_model.symbol_table)
                     .symbol_expr();

  postamble.add(goto_programt::make_decl(check_var));

  postamble.add(goto_programt::make_function_call(code_function_callt{
    check_var,
    library
      .dfcc_fun_symbol
        [dfcc_funt::WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY]
      .symbol_expr(),
    {address_of_write_set}}));

  // TODO add property class on assertion source_location
  source_locationt sl;
  sl.set_function(wrapper_symbol.name);
  sl.set_comment("Check that requires do not allocate or deallocate memory");
  postamble.add(goto_programt::make_assertion(check_var, sl));
  postamble.add(goto_programt::make_dead(check_var));

  // generate write set release and DEAD instructions
  {
    code_function_callt call(
      library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_RELEASE).symbol_expr(),
      {address_of_write_set});
    postamble.add(goto_programt::make_function_call(call));
    postamble.add(goto_programt::make_dead(write_set));
  }
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_requires_write_set()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_ensures_write_set()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_ensures_write_set()"
              << messaget::eom;

  PRECONDITION(ensures_write_set_symbol_opt);
  PRECONDITION(addr_of_ensures_write_set_symbol_opt);

  // call set_create(
  //   ensures_write_set,
  //   assigns_size = 0,
  //   frees_size = 0,
  //   replacement_mode = false,
  //   assume_requires_ctx = false,
  //   assert_requires_ctx = false,
  //   assume_ensures_ctx = contract_mode != check,
  //   assert_ensures_ctx = contract_mode == check,
  // )
  const auto write_set = ensures_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(write_set));

  const auto address_of_write_set =
    addr_of_ensures_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(address_of_write_set));
  preamble.add(goto_programt::make_assignment(
    address_of_write_set, address_of_exprt(write_set)));

  auto function_symbol =
    library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_CREATE).symbol_expr();
  code_function_callt call(function_symbol);
  auto &arguments = call.arguments();

  // write set
  arguments.emplace_back(address_of_write_set);

  // max assigns clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // max frees clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // replacement mode
  arguments.emplace_back((exprt)false_exprt());

  // assume_requires_ctx
  arguments.emplace_back((exprt)false_exprt());

  // assume_requires_ctx
  arguments.emplace_back((exprt)false_exprt());

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    // assume_ensures_ctx
    arguments.emplace_back((exprt)false_exprt());

    // assert_ensures_ctx
    arguments.emplace_back((exprt)true_exprt());
  }
  else
  {
    // assume_ensures_ctx
    arguments.emplace_back((exprt)true_exprt());

    // assert_ensures_ctx
    arguments.emplace_back((exprt)false_exprt());
  }

  preamble.add(goto_programt::make_function_call(call));

  // call link_is_freshr_allocated(pre_post, caller) if we are doing replacement
  if(contract_mode == dfcc_contract_modet::REPLACE)
  {
    auto function_symbol =
      library.dfcc_fun_symbol.at(dfcc_funt::LINK_IS_FRESHR_ALLOCATED)
        .symbol_expr();
    code_function_callt call(function_symbol);
    auto &arguments = call.arguments();
    arguments.emplace_back(address_of_write_set);
    arguments.emplace_back(caller_write_set_symbol.symbol_expr());
    link_caller_write_set.add(goto_programt::make_function_call(call));
  }

  // check for absence of allocation/deallocation in contract clauses
  // ```
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc =
  /// check_empty_alloc_dealloct(write_set, lhs, sizeof(lhs));
  // ASSERT(__check_no_alloc);
  // DEAD __check_no_alloc: bool;
  // ```
  auto check_var = get_fresh_aux_symbol(
                     bool_typet(),
                     id2string(wrapper_symbol.name),
                     "__no_alloc_dealloc_in_ensures_clauses",
                     source_locationt{}, // TODO add property class and comment
                     wrapper_symbol.mode,
                     goto_model.symbol_table)
                     .symbol_expr();

  postamble.add(goto_programt::make_decl(check_var));

  postamble.add(goto_programt::make_function_call(code_function_callt{
    check_var,
    library
      .dfcc_fun_symbol
        [dfcc_funt::WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY]
      .symbol_expr(),
    {address_of_write_set}}));

  // TODO add property class on assertion source_location
  source_locationt sl;
  sl.set_function(wrapper_symbol.name);
  sl.set_comment("Check that ensures do not allocate or deallocate memory");
  postamble.add(goto_programt::make_assertion(check_var, sl));
  postamble.add(goto_programt::make_dead(check_var));

  // generate write set release and DEAD instructions
  {
    code_function_callt call(
      library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_RELEASE).symbol_expr(),
      {address_of_write_set});
    postamble.add(goto_programt::make_function_call(call));
    postamble.add(goto_programt::make_dead(write_set));
  }
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_ensures_write_set()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_contract_write_set()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_contract_write_set()"
              << messaget::eom;

  PRECONDITION(contract_write_set_symbol_opt);

  const auto write_set = contract_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(write_set));

  PRECONDITION(addr_of_contract_write_set_symbol_opt);
  const auto address_of_contract_write_set =
    addr_of_contract_write_set_symbol_opt->symbol_expr();
  preamble.add(goto_programt::make_decl(address_of_contract_write_set));
  preamble.add(goto_programt::make_assignment(
    address_of_contract_write_set, address_of_exprt(write_set)));

  // We use the empty write set used to check ensures for side effects
  // to check for side effects in the assigns and frees functions as well
  PRECONDITION(addr_of_requires_write_set_symbol_opt);
  const auto address_of_requires_write_set =
    addr_of_requires_write_set_symbol_opt->symbol_expr();

  // call set_create
  {
    auto function_symbol =
      library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_CREATE).symbol_expr();

    code_function_callt call(function_symbol);
    auto &arguments = call.arguments();

    // write set
    arguments.emplace_back(address_of_contract_write_set);

    // max assigns clause size
    arguments.emplace_back(
      from_integer(contract_functions.get_nof_assigns_targets(), size_type()));

    // max frees clause size
    arguments.emplace_back(
      from_integer(contract_functions.get_nof_frees_targets(), size_type()));

    // activate replace mode
    const bool replace = contract_mode == dfcc_contract_modet::REPLACE;
    arguments.emplace_back(
      (replace ? (exprt)true_exprt() : (exprt)false_exprt()));

    // assume_requires_ctx
    arguments.emplace_back((exprt)false_exprt());

    // assert_requires_ctx
    arguments.emplace_back((exprt)false_exprt());

    // assume_ensures_ctx
    arguments.emplace_back((exprt)false_exprt());

    // assert_ensures_ctx
    arguments.emplace_back((exprt)false_exprt());

    write_set_checks.add(goto_programt::make_function_call(call));
  }

  // build arguments for assigns and frees clauses functions
  exprt::operandst wrapper_arguments;
  const auto &wrapper_code_type = to_code_type(wrapper_symbol.type);
  for(const auto &parameter : wrapper_code_type.parameter_identifiers())
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);
    wrapper_arguments.push_back(parameter_symbol.symbol_expr());
  }

  // call spec_assigns to build the contract write set
  {
    code_function_callt call(
      contract_functions.get_spec_assigns_function_symbol().symbol_expr());

    auto &arguments = call.arguments();

    // forward wrapper arguments
    for(const auto &arg : wrapper_arguments)
      arguments.push_back(arg);

    // pass write set to populate
    arguments.emplace_back(address_of_contract_write_set);

    // pass the empty write set to check side effects against
    arguments.emplace_back(address_of_requires_write_set);

    write_set_checks.add(goto_programt::make_function_call(call));
  }

  // call spec_frees to build the contract write set
  {
    code_function_callt call(
      contract_functions.get_spec_frees_function_symbol().symbol_expr());
    auto &arguments = call.arguments();

    // forward wrapper arguments
    for(const auto &arg : wrapper_arguments)
      arguments.push_back(arg);

    // pass write set to populate
    arguments.emplace_back(address_of_contract_write_set);

    // pass the empty write set to check side effects against
    arguments.emplace_back(address_of_requires_write_set);

    write_set_checks.add(goto_programt::make_function_call(call));
  }

  // generate write set release and DEAD instructions
  {
    code_function_callt call(
      library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_RELEASE).symbol_expr(),
      {address_of_contract_write_set});
    postamble.add(goto_programt::make_function_call(call));
    postamble.add(goto_programt::make_dead(write_set));
  }
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_contract_write_set()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_requires_clauses()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_requires_clauses()"
              << messaget::eom;
  // we use this empty requires write set to check for the absence of side
  // effects in the requires clauses
  PRECONDITION(addr_of_requires_write_set_symbol_opt);
  const auto &wrapper_id = wrapped_symbol.name;
  const auto &language_mode = utils.get_function_symbol(wrapper_id).mode;

  code_contractst code_contracts(goto_model, log);

  // translate requires clauses
  exprt::operandst requires_conjuncts;
  for(const auto &r : contract_code_type.requires())
  {
    requires_conjuncts.push_back(
      to_lambda_expr(r).application(contract_lambda_parameters));
  }

  // propagate source location to the conjunction
  source_locationt sl =
    requires_conjuncts.empty()
      ? contract_code_type.source_location()
      : contract_code_type.requires().front().source_location();

  sl.set_function(wrapper_symbol.name);

  if(contract_mode == dfcc_contract_modet::REPLACE)
  {
    // if in replacement mode, check that assertions hold in the current context
    sl.set_property_class(ID_precondition);
    sl.set_comment(
      "Check requires clause of contract " + id2string(contract_symbol.name) +
      " for function " + id2string(wrapper_id));
  }

  auto requires = conjunction(requires_conjuncts);
  requires.add_source_location() = sl;

  if(has_subexpr(requires, ID_exists) || has_subexpr(requires, ID_forall))
    code_contracts.add_quantified_variable(requires, language_mode);

  goto_programt requires_program;

  // if in replacement mode, check that assertions hold in the current context,
  // otherwise assume
  const auto &statement_type =
    (contract_mode == dfcc_contract_modet::REPLACE) ? ID_assert : ID_assume;

  codet requires_statement(statement_type, {std::move(requires)});

  requires_statement.add_source_location() = requires.source_location();

  converter.goto_convert(requires_statement, requires_program, language_mode);

  requires_program.instructions.back().source_location_nonconst() = sl;

  const auto address_of_requires_write_set =
    addr_of_requires_write_set_symbol_opt->symbol_expr();

  // rewrite is_fresh predicates
  dfcc_is_fresht is_fresh(library, log);
  is_fresh.rewrite_calls(requires_program, address_of_requires_write_set);

  // rewrite is_freeable predicates
  dfcc_is_freeablet is_freeable(library, log);
  is_freeable.rewrite_calls(requires_program, address_of_requires_write_set);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id, requires_program, address_of_requires_write_set);

  // append resulting program to preconditions section
  preconditions.destructive_append(requires_program);
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_requires_clauses()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_ensures_clauses()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_ensures_clauses()"
              << messaget::eom;
  // we need the contract write set for the freed predicates
  PRECONDITION(addr_of_contract_write_set_symbol_opt);
  // we need the ensures write set to check for side effects
  PRECONDITION(addr_of_ensures_write_set_symbol_opt);
  const auto &language_mode = wrapper_symbol.mode;
  const auto &wrapper_id = wrapper_symbol.name;

  code_contractst code_contracts(goto_model, log);

  // Build the ensures clause program and snapshot program
  exprt::operandst ensures_conjuncts;
  for(const auto &r : contract_code_type.ensures())
  {
    ensures_conjuncts.push_back(
      to_lambda_expr(r).application(contract_lambda_parameters));
  }

  source_locationt sl =
    ensures_conjuncts.empty()
      ? contract_code_type.source_location()
      : contract_code_type.ensures().front().source_location();

  sl.set_function(wrapper_symbol.name);

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    sl.set_property_class(ID_postcondition);
    sl.set_comment(
      "Check ensures clause of contract " + id2string(contract_symbol.name) +
      " for function " + id2string(wrapper_id));
  }

  auto ensures = conjunction(ensures_conjuncts);

  if(has_subexpr(ensures, ID_exists) || has_subexpr(ensures, ID_forall))
    code_contracts.add_quantified_variable(ensures, language_mode);

  const auto &statement_type =
    (contract_mode == dfcc_contract_modet::CHECK) ? ID_assert : ID_assume;

  codet ensures_statement(statement_type, {std::move(ensures)});

  // Generate pair of programs from the ensures statement where:
  // - the first program is the ensures clause with history variables
  // replaced by snapshot variables
  // - second program takes snapshots of the history variables
  std::pair<goto_programt, goto_programt> program_pair =
    code_contracts.create_ensures_instruction(
      ensures_statement, ensures.source_location(), language_mode);
  goto_programt &ensures_program = program_pair.first;
  goto_programt &history_snapshot_program = program_pair.second;

  // inline all calls in the preconditions

  ensures_program.instructions.back().source_location_nonconst() = sl;

  const auto address_of_ensures_write_set =
    addr_of_ensures_write_set_symbol_opt->symbol_expr();

  // rewrite is_freshr predicates
  dfcc_is_fresht is_fresh(library, log);
  is_fresh.rewrite_calls(ensures_program, address_of_ensures_write_set);

  // rewrite is_freed predicates
  // When checking an ensures clause we link the contract write set to the
  // ensures write set to know what was deallocated by the function and pass
  // it to the is_freed predicate and perform the checks
  {
    PRECONDITION(addr_of_contract_write_set_symbol_opt);
    auto function_symbol =
      library.dfcc_fun_symbol.at(dfcc_funt::LINK_DEALLOCATED).symbol_expr();
    code_function_callt call(function_symbol);
    auto &arguments = call.arguments();
    arguments.emplace_back(address_of_ensures_write_set);
    arguments.emplace_back(
      addr_of_contract_write_set_symbol_opt->symbol_expr());
    link_deallocated.add(goto_programt::make_function_call(call));
  }

  dfcc_is_freeablet is_freeable(library, log);
  is_freeable.rewrite_calls(ensures_program, address_of_ensures_write_set);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id, ensures_program, address_of_ensures_write_set);

  // add the snapshot program in the history section
  history.destructive_append(history_snapshot_program);

  // add the ensures program to the postconditions section
  postconditions.destructive_append(ensures_program);
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_ensures_clauses()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_requires_contract_clauses()
{
  log.debug()
    << "->dfcc_dsl_wrapper_programt::encode_requires_contract_clauses()"
    << messaget::eom;

  const auto &requires_contract = contract_code_type.requires_contract();

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    for(auto &expr : requires_contract)
    {
      auto instance =
        to_lambda_expr(expr).application(contract_lambda_parameters);
      INVARIANT(
        can_cast_expr<function_pointer_obeys_contract_exprt>(instance),
        "instance ok");

      assume_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(instance), preconditions);
    }
  }
  else
  {
    for(auto &expr : requires_contract)
    {
      auto instance =
        to_lambda_expr(expr).application(contract_lambda_parameters);
      INVARIANT(
        can_cast_expr<function_pointer_obeys_contract_exprt>(instance),
        "instance ok");

      assert_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(instance),
        ID_precondition,
        preconditions);
    }
  }
  log.debug()
    << "<-dfcc_dsl_wrapper_programt::encode_requires_contract_clauses()"
    << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_ensures_contract_clauses()
{
  log.debug()
    << "->dfcc_dsl_wrapper_programt::encode_ensures_contract_clauses()"
    << messaget::eom;

  const auto &ensures_contract = contract_code_type.ensures_contract();

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    for(auto &expr : ensures_contract)
    {
      assert_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(
          to_lambda_expr(expr).application(contract_lambda_parameters)),
        ID_postcondition,
        postconditions);
    }
  }
  else
  {
    for(auto &expr : ensures_contract)
    {
      assume_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(
          to_lambda_expr(expr).application(contract_lambda_parameters)),
        postconditions);
    }
  }
  log.debug()
    << "<-dfcc_dsl_wrapper_programt::encode_ensures_contract_clauses()"
    << messaget::eom;
}

void dfcc_dsl_wrapper_programt::assert_function_pointer_obeys_contract(
  const function_pointer_obeys_contract_exprt &expr,
  const irep_idt &property_class,
  goto_programt &dest)
{
  function_pointer_contracts.insert(
    expr.contract_symbol_expr().get_identifier());
  source_locationt loc(expr.source_location());
  loc.set_property_class(property_class);
  std::stringstream comment;
  comment << "Assert function pointer '"
          << from_expr_using_mode(
               ns, contract_symbol.mode, expr.function_pointer())
          << "' obeys contract '"
          << from_expr_using_mode(
               ns, contract_symbol.mode, expr.address_of_contract())
          << "'";
  loc.set_comment(comment.str());
  code_assertt assert_expr(
    equal_exprt{expr.function_pointer(), expr.address_of_contract()});
  assert_expr.add_source_location() = loc;
  goto_programt instructions;
  converter.goto_convert(assert_expr, instructions, contract_symbol.mode);
  dest.destructive_append(instructions);
}

void dfcc_dsl_wrapper_programt::assume_function_pointer_obeys_contract(
  const function_pointer_obeys_contract_exprt &expr,
  goto_programt &dest)
{
  log.debug()
    << "->dfcc_dsl_wrapper_programt::assume_function_pointer_obeys_contract("
    << format(expr) << ")" << messaget::eom;

  function_pointer_contracts.insert(
    expr.contract_symbol_expr().get_identifier());

  source_locationt loc(expr.source_location());
  std::stringstream comment;
  comment << "Assume function pointer '"
          << from_expr_using_mode(
               ns, contract_symbol.mode, expr.function_pointer())
          << "' obeys contract '"
          << from_expr_using_mode(
               ns, contract_symbol.mode, expr.contract_symbol_expr())
          << "'";
  loc.set_comment(comment.str());
  dest.add(goto_programt::make_assignment(
    expr.function_pointer(), expr.address_of_contract(), loc));

  log.debug()
    << "<-dfcc_dsl_wrapper_programt::assume_function_pointer_obeys_contract("
    << format(expr) << ")" << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_function_call()
{
  if(contract_mode == dfcc_contract_modet::CHECK)
    encode_checked_function_call();
  else
    encode_havoced_function_call();
}

void dfcc_dsl_wrapper_programt::encode_checked_function_call()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_checked_function_call("
              << wrapped_symbol.name << ")" << messaget::eom;

  PRECONDITION(contract_write_set_symbol_opt);

  // build call to the wrapped function
  code_function_callt call(wrapped_symbol.symbol_expr());

  if(return_value_symbol_opt)
  {
    // DECL
    preamble.add(
      goto_programt::make_decl(return_value_symbol_opt->symbol_expr()));
    call.lhs() = return_value_symbol_opt->symbol_expr();

    // SET_RETURN_VALUE
    postamble.add(goto_programt::make_set_return_value(
      return_value_symbol_opt->symbol_expr()));

    // DEAD
    postamble.add(
      goto_programt::make_dead(return_value_symbol_opt->symbol_expr()));
  }

  // forward wrapper arguments
  const auto &wrapper_code_type = to_code_type(wrapper_symbol.type);

  for(const auto &parameter : wrapper_code_type.parameter_identifiers())
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);
    call.arguments().push_back(parameter_symbol.symbol_expr());
  }

  // pass write set to check against
  call.arguments().push_back(
    addr_of_contract_write_set_symbol_opt->symbol_expr());

  function_call.add(goto_programt::make_function_call(call));

  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_checked_function_call()"
              << messaget::eom;
}

void dfcc_dsl_wrapper_programt::encode_havoced_function_call()
{
  log.debug() << "->dfcc_dsl_wrapper_programt::encode_havoced_function_call()"
              << messaget::eom;

  PRECONDITION(contract_write_set_symbol_opt);

  // generate local write set and add as parameter to the call
  exprt::operandst write_set_arguments;
  for(const auto &parameter :
      to_code_type(wrapper_symbol.type).parameter_identifiers())
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);
    write_set_arguments.push_back(parameter_symbol.symbol_expr());
  }

  auto address_of_contract_write_set =
    addr_of_contract_write_set_symbol_opt->symbol_expr();

  // check assigns clause inclusion
  // IF __caller_write_set==NULL GOTO skip_target;
  // DECL check: bool;
  // CALL check = __CPROVER_contracts_write_set_check_assigns_clause_inclusion(
  //    __caller_write_set, &__local_write_set);
  // ASSERT check;
  // CALL check = __CPROVER_contracts_write_set_check_frees_clause_inclusion(
  //    __caller_write_set, &__local_write_set);
  // ASSERT check;
  // DEAD check;
  // skip_target: skip;

  auto caller_write_set = caller_write_set_symbol.symbol_expr();

  auto goto_instruction =
    write_set_checks.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(caller_write_set)));

  { // assigns clause inclusion
    auto check_var = get_fresh_aux_symbol(
                       bool_typet(),
                       id2string(wrapper_symbol.name),
                       "__check_assigns_clause_incl",
                       source_locationt{},
                       wrapper_symbol.mode,
                       goto_model.symbol_table)
                       .symbol_expr();

    write_set_checks.add(goto_programt::make_decl(check_var));

    code_function_callt check_incl_call(
      check_var,
      library.dfcc_fun_symbol
        .at(dfcc_funt::WRITE_SET_CHECK_ASSIGNS_CLAUSE_INCLUSION)
        .symbol_expr(),
      {caller_write_set, address_of_contract_write_set});

    write_set_checks.add(goto_programt::make_function_call(check_incl_call));

    // TODO use source location of the call site
    source_locationt sl;
    sl.set_function(wrapper_symbol.name);
    sl.set_property_class("assigns");
    sl.set_comment(
      "Check that the assigns clause of " + id2string(contract_symbol.name) +
      " is included in the caller's assigns clause");
    write_set_checks.add(goto_programt::make_assertion(check_var, sl));
    write_set_checks.add(goto_programt::make_dead(check_var));
  }

  { // frees clause inclusion
    auto check_var = get_fresh_aux_symbol(
                       bool_typet(),
                       id2string(wrapper_symbol.name),
                       "__check_frees_clause_incl",
                       source_locationt{},
                       wrapper_symbol.mode,
                       goto_model.symbol_table)
                       .symbol_expr();

    write_set_checks.add(goto_programt::make_decl(check_var));

    code_function_callt check_incl_call(
      check_var,
      library.dfcc_fun_symbol
        .at(dfcc_funt::WRITE_SET_CHECK_FREES_CLAUSE_INCLUSION)
        .symbol_expr(),
      {caller_write_set, address_of_contract_write_set});

    write_set_checks.add(goto_programt::make_function_call(check_incl_call));

    // TODO use source location of the call site
    source_locationt sl;
    sl.set_function(wrapper_symbol.name);
    sl.set_property_class("frees");
    sl.set_comment(
      "Check that the frees clause of " + id2string(contract_symbol.name) +
      " is included in the caller's frees clause");
    write_set_checks.add(goto_programt::make_assertion(check_var, sl));
    write_set_checks.add(goto_programt::make_dead(check_var));
  }

  auto label_instruction = write_set_checks.add(goto_programt::make_skip());
  goto_instruction->complete_goto(label_instruction);

  code_function_callt havoc_call(
    contract_functions.get_spec_assigns_havoc_function_symbol().symbol_expr(),
    {address_of_contract_write_set});

  function_call.add(goto_programt::make_function_call(havoc_call));

  // assign nondet to the return value
  if(return_value_symbol_opt)
  {
    source_locationt location; // TODO create location
    // DECL
    preamble.add(
      goto_programt::make_decl(return_value_symbol_opt->symbol_expr()));

    // ASSIGN NONDET
    auto target = function_call.add(goto_programt::make_assignment(
      return_value_symbol_opt->symbol_expr(),
      side_effect_expr_nondett(return_value_symbol_opt->type, location),
      location));

    // SET RETURN VALUE
    postamble.add(goto_programt::make_set_return_value(
      return_value_symbol_opt->symbol_expr()));

    // DEAD
    postamble.add(
      goto_programt::make_dead(return_value_symbol_opt->symbol_expr()));

    target->code_nonconst().add_source_location() = location;
  }

  // nondet free the freeable set, record effects in both the contract write
  // set and the caller write set
  code_function_callt deallocate_call(
    library.dfcc_fun_symbol.at(dfcc_funt::WRITE_SET_DEALLOCATE_FREEABLE)
      .symbol_expr(),
    {address_of_contract_write_set, caller_write_set});
  function_call.add(goto_programt::make_function_call(deallocate_call));
  log.debug() << "<-dfcc_dsl_wrapper_programt::encode_havoced_function_call()"
              << messaget::eom;
}
