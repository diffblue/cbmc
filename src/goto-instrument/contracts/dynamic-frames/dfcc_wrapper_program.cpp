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
#include "dfcc_library.h"
#include "dfcc_lift_memory_predicates.h"
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
  dfcc_instrumentt &instrument,
  dfcc_lift_memory_predicatest &memory_predicates)
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
    memory_predicates(memory_predicates),
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
                           wrapper_symbol.mode,
                           wrapper_symbol.module,
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
  encode_contract_write_set();
  encode_function_call();
  encode_ensures_clauses();
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
  preamble.add(goto_programt::make_decl(requires_write_set, wrapper_sl));

  preamble.add(
    goto_programt::make_decl(addr_of_requires_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    addr_of_requires_write_set,
    address_of_exprt(requires_write_set),
    wrapper_sl));

  bool check_mode = contract_mode == dfcc_contract_modet::CHECK;
  code_function_callt call = library.write_set_create_call(
    addr_of_requires_write_set,
    from_integer(0, size_type()),
    from_integer(0, size_type()),
    make_boolean_expr(check_mode),
    make_boolean_expr(!check_mode),
    false_exprt(),
    false_exprt(),
    true_exprt(),
    true_exprt(),
    wrapper_sl);

  preamble.add(goto_programt::make_function_call(call, wrapper_sl));

  // check for absence of allocation/deallocation in requires clauses
  // ```c
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc = check_empty_alloc_dealloc(requilres_write_set);
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
    library.write_set_check_allocated_deallocated_is_empty_call(
      check_var, addr_of_requires_write_set, wrapper_sl),
    wrapper_sl));

  source_locationt check_sl(wrapper_sl);
  check_sl.set_function(wrapper_symbol.name);
  check_sl.set_property_class("no_alloc_dealloc_in_requires");
  check_sl.set_comment(
    "Check that requires do not allocate or deallocate memory");
  postamble.add(goto_programt::make_assertion(check_var, check_sl));
  postamble.add(goto_programt::make_dead(check_var, wrapper_sl));

  // generate write set release and DEAD instructions
  postamble.add(goto_programt::make_function_call(
    library.write_set_release_call(addr_of_requires_write_set, wrapper_sl),
    wrapper_sl));
  postamble.add(goto_programt::make_dead(requires_write_set, wrapper_sl));
}

void dfcc_wrapper_programt::encode_ensures_write_set()
{
  // call write_set_create(
  //   ensures_write_set,
  //   assigns_size = 0,
  //   frees_size = 0,
  //   assume_requires_ctx = false,
  //   assert_requires_ctx = false,
  //   assume_ensures_ctx = contract_mode != check,
  //   assert_ensures_ctx = contract_mode == check,
  // )
  preamble.add(goto_programt::make_decl(ensures_write_set, wrapper_sl));

  preamble.add(goto_programt::make_decl(addr_of_ensures_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    addr_of_ensures_write_set,
    address_of_exprt(ensures_write_set),
    wrapper_sl));

  bool check_mode = contract_mode == dfcc_contract_modet::CHECK;

  code_function_callt call = library.write_set_create_call(
    addr_of_ensures_write_set,
    from_integer(0, size_type()),
    from_integer(0, size_type()),
    false_exprt(),
    false_exprt(),
    make_boolean_expr(!check_mode),
    make_boolean_expr(check_mode),
    true_exprt(),
    true_exprt(),
    wrapper_sl);

  preamble.add(goto_programt::make_function_call(call, wrapper_sl));

  // call link_allocated(pre_post, caller) if in REPLACE MODE
  if(contract_mode == dfcc_contract_modet::REPLACE)
  {
    link_allocated_caller.add(goto_programt::make_function_call(
      library.link_allocated_call(
        addr_of_ensures_write_set, caller_write_set, wrapper_sl),
      wrapper_sl));
  }

  // check for absence of allocation/deallocation in contract clauses
  // ```c
  // DECL __check_no_alloc: bool;
  // CALL __check_no_alloc = check_empty_alloc_dealloc(ensures_write_set);
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
    library.write_set_check_allocated_deallocated_is_empty_call(
      check_var, addr_of_ensures_write_set, wrapper_sl),
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
    library.write_set_release_call(addr_of_ensures_write_set, wrapper_sl),
    wrapper_sl));

  // declare write set DEAD
  postamble.add(goto_programt::make_dead(ensures_write_set, wrapper_sl));
}

void dfcc_wrapper_programt::encode_contract_write_set()
{
  preamble.add(goto_programt::make_decl(contract_write_set, wrapper_sl));

  preamble.add(
    goto_programt::make_decl(addr_of_contract_write_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    addr_of_contract_write_set,
    address_of_exprt(contract_write_set),
    wrapper_sl));

  // We use the empty write set used to check ensures for side effects
  // to check for side effects in the assigns and frees functions as well
  // TODO: I don't know what the above comment means, why was there an empty
  // write set here?

  // call write_set_create
  {
    code_function_callt call = library.write_set_create_call(
      addr_of_contract_write_set,
      from_integer(contract_functions.get_nof_assigns_targets(), size_type()),
      from_integer(contract_functions.get_nof_frees_targets(), size_type()),
      false_exprt(),
      false_exprt(),
      false_exprt(),
      false_exprt(),
      true_exprt(),
      true_exprt(),
      wrapper_sl);
    write_set_checks.add(goto_programt::make_function_call(call, wrapper_sl));
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
    arguments.emplace_back(addr_of_contract_write_set);

    // pass the empty write set to check side effects against
    arguments.emplace_back(addr_of_requires_write_set);

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
    arguments.emplace_back(addr_of_contract_write_set);

    // pass the empty write set to check side effects against
    arguments.emplace_back(addr_of_requires_write_set);

    write_set_checks.add(goto_programt::make_function_call(call, wrapper_sl));
  }

  // generate write set release and DEAD instructions
  postamble.add(goto_programt::make_function_call(
    library.write_set_release_call(addr_of_contract_write_set, wrapper_sl),
    wrapper_sl));
  postamble.add(
    goto_programt::make_dead(addr_of_contract_write_set, wrapper_sl));
}

void dfcc_wrapper_programt::encode_is_fresh_set()
{
  preamble.add(goto_programt::make_decl(is_fresh_set, wrapper_sl));

  preamble.add(goto_programt::make_decl(addr_of_is_fresh_set, wrapper_sl));
  preamble.add(goto_programt::make_assignment(
    addr_of_is_fresh_set, address_of_exprt(is_fresh_set), wrapper_sl));

  // CALL obj_set_create_indexed_by_object_id(is_fresh_set) in preamble
  preamble.add(goto_programt::make_function_call(
    library.obj_set_create_indexed_by_object_id_call(
      addr_of_is_fresh_set, wrapper_sl),
    wrapper_sl));

  // link to requires write set
  link_is_fresh.add(goto_programt::make_function_call(
    library.link_is_fresh_call(
      addr_of_requires_write_set, addr_of_is_fresh_set, wrapper_sl),
    wrapper_sl));

  // link to ensures write set
  link_is_fresh.add(goto_programt::make_function_call(
    library.link_is_fresh_call(
      addr_of_ensures_write_set, addr_of_is_fresh_set, wrapper_sl),
    wrapper_sl));

  // release call in postamble
  postamble.add(goto_programt::make_function_call(
    library.obj_set_release_call(addr_of_is_fresh_set, wrapper_sl),
    wrapper_sl));

  // DEAD instructions in postamble
  postamble.add(goto_programt::make_dead(is_fresh_set, wrapper_sl));
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

  // fix calls to user-defined memory predicates
  memory_predicates.fix_calls(requires_program);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id,
    requires_program,
    addr_of_requires_write_set,
    function_pointer_contracts);

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
    exprt ensures = to_lambda_expr(e)
                      .application(contract_lambda_parameters)
                      .with_source_location<exprt>(e);

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

  // When checking an ensures clause we link the contract write set to the
  // ensures write set to know what was deallocated by the function so that
  // the was_freed predicate can perform its checks
  link_deallocated_contract.add(goto_programt::make_function_call(
    library.link_deallocated_call(
      addr_of_ensures_write_set, addr_of_contract_write_set, wrapper_sl),
    wrapper_sl));

  // fix calls to user-defined user-defined memory predicates
  memory_predicates.fix_calls(ensures_program);

  // instrument for side effects
  instrument.instrument_goto_program(
    wrapper_id,
    ensures_program,
    addr_of_ensures_write_set,
    function_pointer_contracts);

  // add the snapshot program in the history section
  history.destructive_append(history_snapshot_program);

  // add the ensures program to the postconditions section
  postconditions.destructive_append(ensures_program);
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

    write_set_checks.add(goto_programt::make_function_call(
      library.write_set_check_assigns_clause_inclusion_call(
        check_var, caller_write_set, addr_of_contract_write_set, wrapper_sl),
      wrapper_sl));

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

    write_set_checks.add(goto_programt::make_function_call(
      library.write_set_check_frees_clause_inclusion_call(
        check_var, caller_write_set, addr_of_contract_write_set, wrapper_sl),
      wrapper_sl));

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
    {addr_of_contract_write_set});

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
  function_call.add(goto_programt::make_function_call(
    library.write_set_deallocate_freeable_call(
      addr_of_contract_write_set, caller_write_set, wrapper_sl),
    wrapper_sl));
}
