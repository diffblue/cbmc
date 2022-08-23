/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_wrapper_program.h"

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
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_contract_functions.h"
#include "dfcc_instrument.h"
#include "dfcc_is_freeable.h"
#include "dfcc_is_fresh.h"
#include "dfcc_library.h"
#include "dfcc_utils.h"

/// Generate the contract write set
const symbol_exprt create_contract_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET],
      id2string(wrapper_symbol.name),
      "__contract_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate the contract write set pointer
const symbol_exprt create_addr_of_contract_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
      id2string(wrapper_symbol.name),
      "__address_of_contract_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

// Generate the write set to check for side effects in requires clauses
const symbol_exprt create_requires_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET],
      id2string(wrapper_symbol.name),
      "__requires_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate the write set pointer to check side effects in requires clauses
const symbol_exprt create_addr_of_requires_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
      id2string(wrapper_symbol.name),
      "__address_of_requires_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate the write set to check side effects in ensures clauses
const symbol_exprt create_ensures_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET],
      id2string(wrapper_symbol.name),
      "__ensures_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate the write set pointer to check side effects in ensures clauses
const symbol_exprt create_addr_of_ensures_write_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::WRITE_SET_PTR],
      id2string(wrapper_symbol.name),
      "__address_of_ensures_write_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate object set used to support is_fresh predicates
const symbol_exprt create_is_fresh_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::OBJ_SET],
      id2string(wrapper_symbol.name),
      "__is_fresh_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

/// Generate object set pointer used to support is_fresh predicates
const symbol_exprt create_addr_of_is_fresh_set(
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  const symbolt &wrapper_symbol)
{
  return utils
    .create_symbol(
      library.dfcc_type[dfcc_typet::OBJ_SET_PTR],
      id2string(wrapper_symbol.name),
      "__address_of_is_fresh_set",
      wrapper_symbol.location,
      wrapper_symbol.mode,
      wrapper_symbol.module,
      false)
    .symbol_expr();
}

dfcc_wrapper_programt::dfcc_wrapper_programt(
  const dfcc_contract_modet contract_mode,
  const symbolt &wrapper_symbol,
  const symbolt &wrapped_symbol,
  const dfcc_contract_functionst &contract_functions,
  const symbolt &caller_write_set_symbol,
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument)
  : contract_mode(contract_mode),
    wrapper_symbol(wrapper_symbol),
    wrapped_symbol(wrapped_symbol),
    contract_functions(contract_functions),
    contract_symbol(contract_functions.pure_contract_symbol),
    contract_code_type(to_code_with_contract_type(contract_symbol.type)),
    caller_write_set(caller_write_set_symbol.symbol_expr()),
    wrapper_sl(wrapper_symbol.location),
    return_value_opt(),
    contract_write_set(
      create_contract_write_set(utils, library, wrapper_symbol)),
    addr_of_contract_write_set(
      create_addr_of_contract_write_set(utils, library, wrapper_symbol)),
    requires_write_set(
      create_requires_write_set(utils, library, wrapper_symbol)),
    addr_of_requires_write_set(
      create_addr_of_requires_write_set(utils, library, wrapper_symbol)),
    ensures_write_set(create_ensures_write_set(utils, library, wrapper_symbol)),
    addr_of_ensures_write_set(
      create_addr_of_ensures_write_set(utils, library, wrapper_symbol)),
    is_fresh_set(create_is_fresh_set(utils, library, wrapper_symbol)),
    addr_of_is_fresh_set(
      create_addr_of_is_fresh_set(utils, library, wrapper_symbol)),
    function_pointer_contracts(),
    goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    instrument(instrument),
    ns(goto_model.symbol_table),
    converter(goto_model.symbol_table, log.get_message_handler())
{
  // generate a return value symbol (needed to instantiate all contract lambdas)
  if(contract_code_type.return_type().id() != ID_empty)
  {
    return_value_opt = utils
                         .create_symbol(
                           contract_code_type.return_type(),
                           id2string(wrapper_symbol.name),
                           "__contract_return_value",
                           wrapper_symbol.location,
                           wrapper_symbol.module,
                           wrapper_symbol.mode,
                           false)
                         .symbol_expr();

    // build contract_lambda_parameters
    contract_lambda_parameters.push_back(return_value_opt.value());
  }

  // build contract_lambda_parameters
  for(const auto &param_id :
      to_code_type(wrapper_symbol.type).parameter_identifiers())
  {
    contract_lambda_parameters.push_back(ns.lookup(param_id).symbol_expr());
  }

  // encode all contract clauses
  encode_requires_write_set();
  encode_ensures_write_set();
  encode_is_fresh_set();
  encode_requires_clauses();
  encode_requires_contract_clauses();
  encode_contract_write_set();
  encode_function_call();
  encode_ensures_clauses();
  encode_ensures_contract_clauses();
}

void dfcc_wrapper_programt::add_to_dest(
  goto_programt &dest,
  std::set<irep_idt> &dest_fp_contracts)
{
  add_to_dest(dest);
  dest_fp_contracts.insert(
    function_pointer_contracts.begin(), function_pointer_contracts.end());
}

void dfcc_wrapper_programt::add_to_dest(goto_programt &dest)
{
  // add code to dest in the right order
  dest.destructive_append(preamble);
  dest.destructive_append(link_is_fresh);
  dest.destructive_append(preconditions);
  dest.destructive_append(history);
  dest.destructive_append(write_set_checks);
  dest.destructive_append(function_call);
  dest.destructive_append(link_allocated_caller);
  dest.destructive_append(link_deallocated_contract);
  dest.destructive_append(postconditions);
  dest.destructive_append(postamble);
}

void dfcc_wrapper_programt::encode_requires_write_set()
{
  // call write_set_create(
  //   requires_write_set,
  //   assigns_size = 0,
  //   frees_size = 0,
  //   replacement_mode = false,
  //   assume_requires_ctx = contract_mode == check,
  //   assert_requires_ctx = contract_mode != check,
  //   assume_ensures_ctx = false,
  //   assert_ensures_ctx = false,
  // )
  const auto write_set = requires_write_set;
  preamble.add(goto_programt::make_decl(write_set, wrapper_sl));

  const auto address_of_write_set = addr_of_requires_write_set;
  preamble.add(goto_programt::make_decl(address_of_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    address_of_write_set, address_of_exprt(write_set), wrapper_sl));

  auto function_symbol =
    library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CREATE].symbol_expr();
  code_function_callt call(function_symbol);
  auto &arguments = call.arguments();

  // write set
  arguments.emplace_back(address_of_write_set);

  // max assigns clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // max frees clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // replacement mode
  arguments.push_back(false_exprt());

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    // assume_requires_ctx
    arguments.push_back(true_exprt());

    // assert_requires_ctx
    arguments.push_back(false_exprt());
  }
  else
  {
    // assume_requires_ctx
    arguments.push_back(false_exprt());

    // assert_requires_ctx mode
    arguments.push_back(true_exprt());
  }

  // assume_ensures_ctx mode
  arguments.push_back(false_exprt());

  // assert_ensures_ctx mode
  arguments.push_back(false_exprt());

  preamble.add(goto_programt::make_function_call(call, wrapper_sl));

  // check for absence of allocation/deallocation in requires clauses
  // ```c
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc = check_empty_alloc_dealloc(write_set);
  // ASSERT __check_no_alloc;
  // DEAD __check_no_alloc: bool;
  // ```
  auto check_var = get_fresh_aux_symbol(
                     bool_typet(),
                     id2string(wrapper_symbol.name),
                     "__no_alloc_dealloc_in_requires",
                     wrapper_sl,
                     wrapper_symbol.mode,
                     goto_model.symbol_table)
                     .symbol_expr();

  postamble.add(goto_programt::make_decl(check_var, wrapper_sl));

  postamble.add(goto_programt::make_function_call(
    code_function_callt{
      check_var,
      library
        .dfcc_fun_symbol
          [dfcc_funt::WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY]
        .symbol_expr(),
      {address_of_write_set}},
    wrapper_sl));

  source_locationt check_sl(wrapper_sl);
  check_sl.set_function(wrapper_symbol.name);
  check_sl.set_property_class("no_alloc_dealloc_in_requires");
  check_sl.set_comment(
    "Check that requires do not allocate or deallocate memory");
  postamble.add(goto_programt::make_assertion(check_var, check_sl));
  postamble.add(goto_programt::make_dead(check_var, wrapper_sl));

  // generate write set release and DEAD instructions
  {
    code_function_callt call(
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RELEASE].symbol_expr(),
      {address_of_write_set});
    postamble.add(goto_programt::make_function_call(call, wrapper_sl));
    postamble.add(goto_programt::make_dead(write_set, wrapper_sl));
  }
}

void dfcc_wrapper_programt::encode_ensures_write_set()
{
  // call write_set_create(
  //   ensures_write_set,
  //   assigns_size = 0,
  //   frees_size = 0,
  //   replacement_mode = false,
  //   assume_requires_ctx = false,
  //   assert_requires_ctx = false,
  //   assume_ensures_ctx = contract_mode != check,
  //   assert_ensures_ctx = contract_mode == check,
  // )
  const auto write_set = ensures_write_set;
  preamble.add(goto_programt::make_decl(write_set, wrapper_sl));

  const auto address_of_write_set = addr_of_ensures_write_set;
  preamble.add(goto_programt::make_decl(address_of_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    address_of_write_set, address_of_exprt(write_set), wrapper_sl));

  auto function_symbol =
    library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CREATE].symbol_expr();
  code_function_callt call(function_symbol);
  auto &arguments = call.arguments();

  // write set
  arguments.emplace_back(address_of_write_set);

  // max assigns clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // max frees clause size
  arguments.emplace_back(from_integer(0, size_type()));

  // replacement mode
  arguments.push_back(false_exprt());

  // assume_requires_ctx
  arguments.push_back(false_exprt());

  // assume_requires_ctx
  arguments.push_back(false_exprt());

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    // assume_ensures_ctx
    arguments.push_back(false_exprt());

    // assert_ensures_ctx
    arguments.push_back(true_exprt());
  }
  else
  {
    // assume_ensures_ctx
    arguments.push_back(true_exprt());

    // assert_ensures_ctx
    arguments.push_back(false_exprt());
  }

  preamble.add(goto_programt::make_function_call(call));

  // call link_allocated(pre_post, caller) if in REPLACE MODE
  if(contract_mode == dfcc_contract_modet::REPLACE)
  {
    auto function_symbol =
      library.dfcc_fun_symbol[dfcc_funt::LINK_ALLOCATED].symbol_expr();
    code_function_callt call(function_symbol);
    auto &arguments = call.arguments();
    arguments.emplace_back(address_of_write_set);
    arguments.emplace_back(caller_write_set);
    link_allocated_caller.add(
      goto_programt::make_function_call(call, wrapper_sl));
  }

  // check for absence of allocation/deallocation in contract clauses
  // ```c
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc = check_empty_alloc_dealloc(write_set);
  // ASSERT __check_no_alloc;
  // DEAD __check_no_alloc: bool;
  // ```
  auto check_var = get_fresh_aux_symbol(
                     bool_typet(),
                     id2string(wrapper_symbol.name),
                     "__no_alloc_dealloc_in_ensures_clauses",
                     wrapper_sl,
                     wrapper_symbol.mode,
                     goto_model.symbol_table)
                     .symbol_expr();

  postamble.add(goto_programt::make_decl(check_var, wrapper_sl));

  postamble.add(goto_programt::make_function_call(
    code_function_callt{
      check_var,
      library
        .dfcc_fun_symbol
          [dfcc_funt::WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY]
        .symbol_expr(),
      {address_of_write_set}},
    wrapper_sl));

  source_locationt check_sl(wrapper_sl);
  check_sl.set_function(wrapper_symbol.name);
  check_sl.set_property_class("no_alloc_dealloc_in_ensures");
  check_sl.set_comment(
    "Check that ensures do not allocate or deallocate memory");

  postamble.add(goto_programt::make_assertion(check_var, check_sl));
  postamble.add(goto_programt::make_dead(check_var, wrapper_sl));

  // generate write set release
  postamble.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RELEASE].symbol_expr(),
      {address_of_write_set}},
    wrapper_sl));

  // declare write set DEAD
  postamble.add(goto_programt::make_dead(write_set, wrapper_sl));
}

void dfcc_wrapper_programt::encode_contract_write_set()
{
  const auto write_set = contract_write_set;
  preamble.add(goto_programt::make_decl(write_set, wrapper_sl));

  const auto address_of_contract_write_set = addr_of_contract_write_set;
  preamble.add(
    goto_programt::make_decl(address_of_contract_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    address_of_contract_write_set, address_of_exprt(write_set), wrapper_sl));

  // We use the empty write set used to check ensures for side effects
  // to check for side effects in the assigns and frees functions as well
  const auto address_of_requires_write_set = addr_of_requires_write_set;

  // call write_set_create
  {
    auto function_symbol =
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CREATE].symbol_expr();

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

    // not analysing ensures or requires clauses, set all context flags to false

    // assume_requires_ctx
    arguments.push_back(false_exprt());

    // assert_requires_ctx
    arguments.push_back(false_exprt());

    // assume_ensures_ctx
    arguments.push_back(false_exprt());

    // assert_ensures_ctx
    arguments.push_back(false_exprt());

    write_set_checks.add(goto_programt::make_function_call(call));
  }

  // build arguments for assigns and frees clauses functions
  exprt::operandst wrapper_arguments;
  const auto &wrapper_code_type = to_code_type(wrapper_symbol.type);
  for(const auto &parameter : wrapper_code_type.parameter_identifiers())
  {
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

    write_set_checks.add(goto_programt::make_function_call(call, wrapper_sl));
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

    write_set_checks.add(goto_programt::make_function_call(call, wrapper_sl));
  }

  // generate write set release and DEAD instructions
  {
    code_function_callt call(
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_RELEASE].symbol_expr(),
      {address_of_contract_write_set});
    postamble.add(goto_programt::make_function_call(call, wrapper_sl));
    postamble.add(goto_programt::make_dead(write_set, wrapper_sl));
  }
}

void dfcc_wrapper_programt::encode_is_fresh_set()
{
  const auto object_set = is_fresh_set;
  preamble.add(goto_programt::make_decl(object_set, wrapper_sl));

  const auto address_of_object_set = addr_of_is_fresh_set;
  preamble.add(goto_programt::make_decl(address_of_object_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    address_of_object_set, address_of_exprt(object_set), wrapper_sl));

  // CALL obj_set_create_indexed_by_object_id(is_fresh_set) in preamble
  preamble.add(goto_programt::make_function_call(
    code_function_callt{
      library.dfcc_fun_symbol[dfcc_funt::OBJ_SET_CREATE_INDEXED_BY_OBJECT_ID]
        .symbol_expr(),
      {address_of_object_set}},
    wrapper_sl));

  // link to requires write set
  link_is_fresh.add(goto_programt::make_function_call(
    code_function_callt(
      library.dfcc_fun_symbol[dfcc_funt::LINK_IS_FRESH].symbol_expr(),
      {addr_of_requires_write_set, address_of_object_set}),
    wrapper_sl));

  // link to ensures write set
  link_is_fresh.add(goto_programt::make_function_call(
    code_function_callt(
      library.dfcc_fun_symbol[dfcc_funt::LINK_IS_FRESH].symbol_expr(),
      {addr_of_ensures_write_set, address_of_object_set}),
    wrapper_sl));

  // release call in postamble
  postamble.add(goto_programt::make_function_call(
    code_function_callt(
      library.dfcc_fun_symbol[dfcc_funt::OBJ_SET_RELEASE].symbol_expr(),
      {address_of_object_set}),
    wrapper_sl));

  // DEAD instructions in postamble
  postamble.add(goto_programt::make_dead(object_set, wrapper_sl));
}

void dfcc_wrapper_programt::encode_requires_clauses()
{
  // we use this empty requires write set to check for the absence of side
  // effects in the requires clauses
  const auto &wrapper_id = wrapper_symbol.name;
  const auto &language_mode = utils.get_function_symbol(wrapper_id).mode;

  // if in replacement mode, check that assertions hold in the current context,
  // otherwise assume
  const auto &statement_type =
    (contract_mode == dfcc_contract_modet::REPLACE) ? ID_assert : ID_assume;

  // goto program where all requires are added
  goto_programt requires_program;

  // translate each requires clause
  for(const auto &r : contract_code_type.requires())
  {
    exprt requires = to_lambda_expr(r).application(contract_lambda_parameters);
    requires.add_source_location() = r.source_location();
    if(has_subexpr(requires, ID_exists) || has_subexpr(requires, ID_forall))
      add_quantified_variable(goto_model.symbol_table, requires, language_mode);

    source_locationt sl(r.source_location());
    if(statement_type == ID_assert)
    {
      sl.set_property_class(ID_precondition);
      sl.set_comment(
        "Check requires clause of contract " + id2string(contract_symbol.name) +
        " for function " + id2string(wrapper_id));
    }
    codet requires_statement(statement_type, {std::move(requires)}, sl);
    converter.goto_convert(requires_statement, requires_program, language_mode);
  }

  const auto address_of_requires_write_set = addr_of_requires_write_set;

  // rewrite is_fresh predicates
  dfcc_is_fresht is_fresh(library, message_handler);
  is_fresh.rewrite_calls(requires_program, address_of_requires_write_set);

  // rewrite is_freeable predicates
  dfcc_is_freeablet is_freeable(library, message_handler);
  is_freeable.rewrite_calls(requires_program, address_of_requires_write_set);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id, requires_program, address_of_requires_write_set);

  // append resulting program to preconditions section
  preconditions.destructive_append(requires_program);
}

void dfcc_wrapper_programt::encode_ensures_clauses()
{
  const auto &language_mode = wrapper_symbol.mode;
  const auto &wrapper_id = wrapper_symbol.name;
  const auto &statement_type =
    (contract_mode == dfcc_contract_modet::CHECK) ? ID_assert : ID_assume;

  // goto program where all history variable snapshots are added
  goto_programt history_snapshot_program;

  // goto program where all requires are added
  goto_programt ensures_program;

  // translate each ensures clause
  for(const auto &e : contract_code_type.ensures())
  {
    exprt ensures = to_lambda_expr(e).application(contract_lambda_parameters);
    ensures.add_source_location() = e.source_location();

    if(has_subexpr(ensures, ID_exists) || has_subexpr(ensures, ID_forall))
      add_quantified_variable(goto_model.symbol_table, ensures, language_mode);

    // this also rewrites ID_old expressions to fresh variables
    generate_history_variables_initialization(
      goto_model.symbol_table,
      ensures,
      language_mode,
      history_snapshot_program);

    source_locationt sl(e.source_location());
    if(statement_type == ID_assert)
    {
      sl.set_property_class(ID_postcondition);
      sl.set_comment(
        "Check ensures clause of contract " + id2string(contract_symbol.name) +
        " for function " + id2string(wrapper_id));
    }

    codet ensures_statement(statement_type, {std::move(ensures)}, sl);
    converter.goto_convert(ensures_statement, ensures_program, language_mode);
  }

  const auto address_of_ensures_write_set = addr_of_ensures_write_set;

  // rewrite is_fresh predicates
  dfcc_is_fresht is_fresh(library, message_handler);
  is_fresh.rewrite_calls(ensures_program, address_of_ensures_write_set);

  // rewrite was_freed predicates
  // When checking an ensures clause we link the contract write set to the
  // ensures write set to know what was deallocated by the function and pass
  // it to the was_freed predicate and perform the checks
  {
    auto function_symbol =
      library.dfcc_fun_symbol[dfcc_funt::LINK_DEALLOCATED].symbol_expr();
    code_function_callt call(function_symbol);
    auto &arguments = call.arguments();
    arguments.emplace_back(address_of_ensures_write_set);
    arguments.emplace_back(addr_of_contract_write_set);
    link_deallocated_contract.add(
      goto_programt::make_function_call(call, wrapper_sl));
  }

  dfcc_is_freeablet is_freeable(library, message_handler);
  is_freeable.rewrite_calls(ensures_program, address_of_ensures_write_set);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id, ensures_program, address_of_ensures_write_set);

  // add the snapshot program in the history section
  history.destructive_append(history_snapshot_program);

  // add the ensures program to the postconditions section
  postconditions.destructive_append(ensures_program);
}

void dfcc_wrapper_programt::encode_requires_contract_clauses()
{
  const auto &requires_contract = contract_code_type.requires_contract();

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    for(auto &expr : requires_contract)
    {
      auto instance =
        to_lambda_expr(expr).application(contract_lambda_parameters);
      instance.add_source_location() = expr.source_location();
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
      instance.add_source_location() = expr.source_location();
      INVARIANT(
        can_cast_expr<function_pointer_obeys_contract_exprt>(instance),
        "instance ok");

      assert_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(instance),
        ID_precondition,
        preconditions);
    }
  }
}

void dfcc_wrapper_programt::encode_ensures_contract_clauses()
{
  const auto &ensures_contract = contract_code_type.ensures_contract();

  if(contract_mode == dfcc_contract_modet::CHECK)
  {
    for(auto &expr : ensures_contract)
    {
      auto instance =
        to_lambda_expr(expr).application(contract_lambda_parameters);
      instance.add_source_location() = expr.source_location();
      INVARIANT(
        can_cast_expr<function_pointer_obeys_contract_exprt>(instance),
        "instance ok");
      assert_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(instance),
        ID_postcondition,
        postconditions);
    }
  }
  else
  {
    for(auto &expr : ensures_contract)
    {
      auto instance =
        to_lambda_expr(expr).application(contract_lambda_parameters);
      instance.add_source_location() = expr.source_location();
      INVARIANT(
        can_cast_expr<function_pointer_obeys_contract_exprt>(instance),
        "instance ok");
      assume_function_pointer_obeys_contract(
        to_function_pointer_obeys_contract_expr(instance), postconditions);
    }
  }
}

void dfcc_wrapper_programt::assert_function_pointer_obeys_contract(
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

void dfcc_wrapper_programt::assume_function_pointer_obeys_contract(
  const function_pointer_obeys_contract_exprt &expr,
  goto_programt &dest)
{
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
}

void dfcc_wrapper_programt::encode_function_call()
{
  if(contract_mode == dfcc_contract_modet::CHECK)
    encode_checked_function_call();
  else
    encode_havoced_function_call();
}

void dfcc_wrapper_programt::encode_checked_function_call()
{
  // build call to the wrapped function
  code_function_callt call(wrapped_symbol.symbol_expr());

  if(return_value_opt)
  {
    symbol_exprt return_value = return_value_opt.value();
    // DECL
    preamble.add(goto_programt::make_decl(return_value, wrapper_sl));
    call.lhs() = return_value;

    // SET_RETURN_VALUE
    postamble.add(
      goto_programt::make_set_return_value(return_value, wrapper_sl));

    // DEAD
    postamble.add(goto_programt::make_dead(return_value, wrapper_sl));
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
  call.arguments().push_back(addr_of_contract_write_set);

  function_call.add(goto_programt::make_function_call(call, wrapper_sl));
}

void dfcc_wrapper_programt::encode_havoced_function_call()
{
  // generate local write set and add as parameter to the call
  exprt::operandst write_set_arguments;
  for(const auto &parameter :
      to_code_type(wrapper_symbol.type).parameter_identifiers())
  {
    PRECONDITION(!parameter.empty());
    const symbolt &parameter_symbol = ns.lookup(parameter);
    write_set_arguments.push_back(parameter_symbol.symbol_expr());
  }

  auto address_of_contract_write_set = addr_of_contract_write_set;

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

  auto goto_instruction =
    write_set_checks.add(goto_programt::make_incomplete_goto(
      utils.make_null_check_expr(caller_write_set), wrapper_sl));

  {
    // assigns clause inclusion
    auto check_var = get_fresh_aux_symbol(
                       bool_typet(),
                       id2string(wrapper_symbol.name),
                       "__check_assigns_clause_incl",
                       wrapper_sl,
                       wrapper_symbol.mode,
                       goto_model.symbol_table)
                       .symbol_expr();

    write_set_checks.add(goto_programt::make_decl(check_var, wrapper_sl));

    code_function_callt check_incl_call(
      check_var,
      library
        .dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_ASSIGNS_CLAUSE_INCLUSION]
        .symbol_expr(),
      {caller_write_set, address_of_contract_write_set});

    write_set_checks.add(
      goto_programt::make_function_call(check_incl_call, wrapper_sl));
    source_locationt check_sl(wrapper_sl);
    check_sl.set_function(wrapper_symbol.name);
    check_sl.set_property_class("assigns");
    check_sl.set_comment(
      "Check that the assigns clause of " + id2string(contract_symbol.name) +
      " is included in the caller's assigns clause");
    write_set_checks.add(goto_programt::make_assertion(check_var, check_sl));
    write_set_checks.add(goto_programt::make_dead(check_var, wrapper_sl));
  }

  {
    // frees clause inclusion
    auto check_var = get_fresh_aux_symbol(
                       bool_typet(),
                       id2string(wrapper_symbol.name),
                       "__check_frees_clause_incl",
                       wrapper_sl,
                       wrapper_symbol.mode,
                       goto_model.symbol_table)
                       .symbol_expr();

    write_set_checks.add(goto_programt::make_decl(check_var, wrapper_sl));

    code_function_callt check_incl_call(
      check_var,
      library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_CHECK_FREES_CLAUSE_INCLUSION]
        .symbol_expr(),
      {caller_write_set, address_of_contract_write_set});

    write_set_checks.add(
      goto_programt::make_function_call(check_incl_call, wrapper_sl));

    source_locationt check_sl(wrapper_sl);
    check_sl.set_function(wrapper_symbol.name);
    check_sl.set_property_class("frees");
    check_sl.set_comment(
      "Check that the frees clause of " + id2string(contract_symbol.name) +
      " is included in the caller's frees clause");
    write_set_checks.add(goto_programt::make_assertion(check_var, check_sl));
    write_set_checks.add(goto_programt::make_dead(check_var, wrapper_sl));
  }

  auto label_instruction = write_set_checks.add(goto_programt::make_skip());
  goto_instruction->complete_goto(label_instruction);

  code_function_callt havoc_call(
    contract_functions.get_spec_assigns_havoc_function_symbol().symbol_expr(),
    {address_of_contract_write_set});

  function_call.add(goto_programt::make_function_call(havoc_call, wrapper_sl));

  // assign nondet to the return value
  if(return_value_opt.has_value())
  {
    symbol_exprt return_value = return_value_opt.value();

    // DECL
    preamble.add(goto_programt::make_decl(return_value, wrapper_sl));

    // ASSIGN NONDET
    function_call.add(goto_programt::make_assignment(
      return_value,
      side_effect_expr_nondett(return_value.type(), wrapper_sl),
      wrapper_sl));

    // SET RETURN VALUE
    postamble.add(
      goto_programt::make_set_return_value(return_value, wrapper_sl));

    // DEAD
    postamble.add(goto_programt::make_dead(return_value, wrapper_sl));
  }

  // nondet free the freeable set, record effects in both the contract write
  // set and the caller write set
  code_function_callt deallocate_call(
    library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_DEALLOCATE_FREEABLE]
      .symbol_expr(),
    {address_of_contract_write_set, caller_write_set});
  function_call.add(
    goto_programt::make_function_call(deallocate_call, wrapper_sl));
}
