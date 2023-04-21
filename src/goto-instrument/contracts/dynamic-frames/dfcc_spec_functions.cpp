/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

#include "dfcc_spec_functions.h"
#include <goto-programs/goto_convert_class.h>

#include <util/format_expr.h>
#include <util/namespace.h>

#include <goto-programs/goto_model.h>

#include <langapi/language_util.h>

#include "dfcc_library.h"
#include "dfcc_utils.h"

dfcc_spec_functionst::dfcc_spec_functionst(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument)
  : goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    instrument(instrument),
    ns(goto_model.symbol_table)
{
}

const typet &dfcc_spec_functionst::get_target_type(const exprt &expr)
{
  INVARIANT(
    expr.id() == ID_typecast && expr.type().id() == ID_pointer &&
      expr.operands().at(0).id() == ID_address_of,
    "target expression must be of the form `cast(address_of(target), empty*)`");

  return expr.operands().at(0).operands().at(0).type();
}

void dfcc_spec_functionst::generate_havoc_function(
  const irep_idt &function_id,
  const irep_idt &havoc_function_id,
  std::size_t &nof_targets)
{
  INVARIANT(
    !goto_model.symbol_table.has_symbol(havoc_function_id),
    "DFCC: havoc function id '" + id2string(havoc_function_id) +
      "' already exists");

  const auto &function_symbol = utils.get_function_symbol(function_id);

  // create the write_set symbol used as input by the havoc function
  const auto &write_set_symbol = utils.create_symbol(
    library.dfcc_type[dfcc_typet::CAR_SET_PTR],
    id2string(havoc_function_id),
    "__write_set_to_havoc",
    function_symbol.location,
    function_symbol.mode,
    function_symbol.module,
    true);

  // create the code type that goes on the function symbol
  code_typet::parametert write_set_param(write_set_symbol.type);
  write_set_param.set_base_name(write_set_symbol.base_name);
  write_set_param.set_identifier(write_set_symbol.name);
  code_typet havoc_code_type({write_set_param}, empty_typet());

  // create the havoc function symbol
  symbolt havoc_function_symbol;
  havoc_function_symbol.base_name = havoc_function_id;
  havoc_function_symbol.name = havoc_function_id;
  havoc_function_symbol.pretty_name = havoc_function_id;
  havoc_function_symbol.type = havoc_code_type;
  havoc_function_symbol.mode = function_symbol.mode;
  havoc_function_symbol.module = function_symbol.module;
  havoc_function_symbol.location = function_symbol.location;
  havoc_function_symbol.set_compiled();
  bool add_function_failed = goto_model.symbol_table.add(havoc_function_symbol);
  INVARIANT(
    !add_function_failed,
    "DFCC: could not insert havoc function '" + id2string(havoc_function_id) +
      "' in the symbol table");

  // create new goto_function
  goto_functiont dummy_havoc_function;
  dummy_havoc_function.set_parameter_identifiers(havoc_code_type);
  goto_model.goto_functions.function_map[havoc_function_id].copy_from(
    dummy_havoc_function);

  // body will be filled with instructions
  auto &havoc_program =
    goto_model.goto_functions.function_map.at(havoc_function_id).body;

  const goto_programt &original_program =
    goto_model.goto_functions.function_map.at(function_id).body;

  generate_havoc_instructions(
    havoc_function_id,
    havoc_function_symbol.mode,
    havoc_function_symbol.module,
    original_program,
    write_set_symbol.symbol_expr(),
    havoc_program,
    nof_targets);

  goto_model.goto_functions.update();

  std::set<irep_idt> no_body;
  std::set<irep_idt> missing_function;
  std::set<irep_idt> recursive_call;
  std::set<irep_idt> not_enough_arguments;
  utils.inline_function(
    havoc_function_id,
    no_body,
    recursive_call,
    missing_function,
    not_enough_arguments);
  INVARIANT(
    no_body.empty(),
    "no body warnings when inlining " + id2string(havoc_function_id));
  INVARIANT(
    missing_function.empty(),
    "missing function warnings when inlining " + id2string(havoc_function_id));
  INVARIANT(
    recursive_call.empty(),
    "recursive calls when inlining " + id2string(havoc_function_id));
  INVARIANT(
    not_enough_arguments.empty(),
    "not enough arguments when inlining " + id2string(havoc_function_id));

  goto_model.goto_functions.function_map.at(havoc_function_id).make_hidden();

  goto_model.goto_functions.update();
}

void dfcc_spec_functionst::generate_havoc_instructions(
  const irep_idt &function_id,
  const irep_idt &mode,
  const irep_idt &module,
  const goto_programt &original_program,
  const exprt &write_set_to_havoc,
  goto_programt &havoc_program,
  std::size_t &nof_targets)
{
  // index of the CAR to havoc in the write set
  std::size_t next_idx = 0;

  // iterate on the body of the original function and emit one havoc instruction
  // per target
  forall_goto_program_instructions(ins_it, original_program)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        throw invalid_source_file_exceptiont(
          "Function pointer calls are not supported in assigns clauses: '" +
            from_expr(ns, function_id, ins_it->call_function()) +
            "' called in function '" + id2string(function_id) + "'",
          ins_it->source_location());
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // Only process built-in functions that represent assigns clause targets,
      // and error-out on any other function call

      // Find the corresponding instrumentation hook
      auto hook_opt = library.get_havoc_hook(callee_id);
      INVARIANT(
        hook_opt.has_value(),
        "dfcc_spec_functionst::generate_havoc_instructions: function calls "
        "must be inlined before calling this function");

      // Use same source location as original call
      source_locationt location(ins_it->source_location());
      auto hook = hook_opt.value();
      code_function_callt call(
        library.dfcc_fun_symbol.at(hook).symbol_expr(),
        {write_set_to_havoc, from_integer(next_idx, size_type())});

      if(hook == dfcc_funt::WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET)
      {
        // ```
        // DECL __havoc_target;
        // CALL __havoc_target = havoc_hook(set, next_idx);
        // IF !__havoc_target GOTO label;
        // ASSIGN *__havoc_target = nondet(target_type);
        // label: DEAD __havoc_target;
        // ```
        // declare a local var to store targets havoced via nondet assignment
        auto &target_type = get_target_type(ins_it->call_arguments().at(0));

        const auto &target_symbol = utils.create_symbol(
          pointer_type(target_type),
          id2string(function_id),
          "__havoc_target",
          location,
          mode,
          module,
          false);

        auto target_expr = target_symbol.symbol_expr();
        havoc_program.add(goto_programt::make_decl(target_expr));

        call.lhs() = target_expr;
        havoc_program.add(goto_programt::make_function_call(call, location));

        auto goto_instruction =
          havoc_program.add(goto_programt::make_incomplete_goto(
            utils.make_null_check_expr(target_expr), location));

        // create nondet assignment to the target
        side_effect_expr_nondett nondet(target_type, location);
        havoc_program.add(goto_programt::make_assignment(
          dereference_exprt{typecast_exprt::conditional_cast(
            target_expr, pointer_type(target_type))},
          nondet,
          location));
        auto label = havoc_program.add(goto_programt::make_dead(target_expr));
        goto_instruction->complete_goto(label);
      }
      else if(
        hook == dfcc_funt::WRITE_SET_HAVOC_OBJECT_WHOLE ||
        hook == dfcc_funt::WRITE_SET_HAVOC_SLICE)
      {
        // ```
        // CALL havoc_hook(set, next_idx);
        // ```
        havoc_program.add(goto_programt::make_function_call(call, location));
      }
      else
      {
        UNREACHABLE;
      }
      ++next_idx;
    }
  }
  nof_targets = next_idx;
  havoc_program.add(goto_programt::make_end_function());
}

void dfcc_spec_functionst::to_spec_assigns_function(
  const irep_idt &function_id,
  std::size_t &nof_targets)
{
  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  // add write_set parameter
  const exprt write_set_to_fill =
    utils
      .add_parameter(
        function_id,
        "__write_set_to_fill",
        library.dfcc_type[dfcc_typet::WRITE_SET_PTR])
      .symbol_expr();

  to_spec_assigns_instructions(
    write_set_to_fill,
    utils.get_function_symbol(function_id).mode,
    goto_function.body,
    nof_targets);

  goto_model.goto_functions.update();

  // instrument for side-effects checking
  std::set<irep_idt> function_pointer_contracts;
  instrument.instrument_function(function_id, function_pointer_contracts);
  INVARIANT(
    function_pointer_contracts.empty(),
    "discovered function pointer contracts unexpectedly");
  goto_model.goto_functions.function_map.at(function_id).make_hidden();
}

void dfcc_spec_functionst::to_spec_assigns_instructions(
  const exprt &write_set_to_fill,
  const irep_idt &language_mode,
  goto_programt &program,
  std::size_t &nof_targets)
{
  // counts the number of calls to built-ins to get an over approximation
  // of the size of the set
  std::size_t next_idx = 0;

  // rewrite calls
  Forall_goto_program_instructions(ins_it, program)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        throw invalid_source_file_exceptiont(
          "Function pointer calls are not supported in assigns clauses '" +
            from_expr_using_mode(ns, language_mode, ins_it->call_function()) +
            "'",
          ins_it->source_location());
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // Only process built-in functions that specify assignable targets
      // and error-out on any other function call

      // Find the corresponding instrumentation hook
      INVARIANT(
        library.is_front_end_builtin(callee_id),
        "dfcc_spec_functionst::to_spec_assigns_function: function calls must "
        "be inlined before calling this function");

      auto hook = library.get_hook(callee_id);
      // redirect the call to the hook
      ins_it->call_function() = library.dfcc_fun_symbol.at(hook).symbol_expr();
      // insert insertion index argument
      ins_it->call_arguments().insert(
        ins_it->call_arguments().begin(), from_integer(next_idx, size_type()));
      // insert write set argument
      ins_it->call_arguments().insert(
        ins_it->call_arguments().begin(), write_set_to_fill);

      // remove the is_pointer_to_pointer argument which is not used in the
      // hook for insert assignable
      if(hook == dfcc_funt::WRITE_SET_INSERT_ASSIGNABLE)
        ins_it->call_arguments().pop_back();

      ++next_idx;
    }
  }
  nof_targets = next_idx;
}

void dfcc_spec_functionst::to_spec_frees_function(
  const irep_idt &function_id,
  std::size_t &nof_targets)
{
  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  // add __dfcc_set parameter
  const exprt &write_set_to_fill =
    utils
      .add_parameter(
        function_id,
        "__write_set_to_fill",
        library.dfcc_type[dfcc_typet::WRITE_SET_PTR])
      .symbol_expr();

  to_spec_frees_instructions(
    write_set_to_fill,
    utils.get_function_symbol(function_id).mode,
    goto_function.body,
    nof_targets);

  goto_model.goto_functions.update();

  // instrument for side-effects checking
  std::set<irep_idt> function_pointer_contracts;
  instrument.instrument_function(function_id, function_pointer_contracts);
  INVARIANT(
    function_pointer_contracts.empty(),
    "discovered function pointer contracts unexpectedly");
  goto_model.goto_functions.function_map.at(function_id).make_hidden();
}

void dfcc_spec_functionst::to_spec_frees_instructions(
  const exprt &write_set_to_fill,
  const irep_idt &language_mode,
  goto_programt &program,
  std::size_t &nof_targets)
{
  // counts the number of calls to the `freeable` builtin
  std::size_t next_idx = 0;
  Forall_goto_program_instructions(ins_it, program)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        throw invalid_source_file_exceptiont(
          "Function pointer calls are not supported in frees clauses: '" +
            from_expr_using_mode(ns, language_mode, ins_it->call_function()) +
            "'",
          ins_it->source_location());
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // only process the built-in `freeable` function
      // error out on any other function call
      INVARIANT(
        callee_id == CPROVER_PREFIX "freeable",
        "dfcc_spec_functionst::to_spec_frees_function: function calls must "
        "be inlined before calling this function");

      ins_it->call_function() =
        library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_ADD_FREEABLE]
          .symbol_expr();
      ins_it->call_arguments().insert(
        ins_it->call_arguments().begin(), write_set_to_fill);
      ++next_idx;
    }
  }

  nof_targets = next_idx;
}
