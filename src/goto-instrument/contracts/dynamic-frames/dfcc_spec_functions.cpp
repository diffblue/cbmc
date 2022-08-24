/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com

\*******************************************************************/

#include "dfcc_spec_functions.h"
#include <goto-programs/goto_convert_class.h>

#include <util/format_expr.h>
#include <util/namespace.h>

#include <goto-programs/goto_model.h>

#include "dfcc_library.h"
#include "dfcc_utils.h"

dfcc_spec_functionst::dfcc_spec_functionst(
  goto_modelt &goto_model,
  messaget &log,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument)
  : goto_model(goto_model),
    log(log),
    message_handler(log.get_message_handler()),
    utils(utils),
    library(library),
    instrument(instrument),
    ns(goto_model.symbol_table)
{
}

bool dfcc_spec_functionst::is_assignable_t_function(const irep_idt &function_id)
{
  auto &symbol = utils.get_function_symbol(function_id);
  auto &return_type = to_code_type(symbol.type).return_type();
  return return_type.id() == ID_empty &&
         return_type.get(ID_C_typedef) == CPROVER_PREFIX "assignable_t";
}

bool dfcc_spec_functionst::is_freeable_t_function(const irep_idt &function_id)
{
  auto &symbol = utils.get_function_symbol(function_id);
  auto &return_type = to_code_type(symbol.type).return_type();
  return return_type.id() == ID_empty &&
         return_type.get(ID_C_typedef) == CPROVER_PREFIX "freeable_t";
}

const typet &dfcc_spec_functionst::get_target_type(const exprt &expr)
{
  if(expr.id() != ID_typecast || expr.type().id() != ID_pointer)
  {
    goto ERROR;
  }

  if(expr.operands().at(0).id() != ID_address_of)
  {
    goto ERROR;
  }

  return expr.operands().at(0).operands().at(0).type();

ERROR:
  log.error() << "dfcc_spec_functionst::get_target_type: expression "
              << format(expr)
              << " is not of the form `cast(address_of(target), empty*)`"
              << messaget::eom;
  exit(0);
}

void dfcc_spec_functionst::generate_havoc_function(
  const irep_idt &function_id,
  const irep_idt &havoc_function_id,
  int &nof_targets)
{
  if(goto_model.symbol_table.has_symbol(havoc_function_id))
  {
    log.error() << "dfcc_spec_functionst::generate_havoc_function: '"
                << havoc_function_id << "' already exists" << messaget::eom;
    exit(0);
  }

  const auto &function_symbol = utils.get_function_symbol(function_id);

  // create the write_set symbol used as input by the havoc function
  const auto &write_set_symbol = utils.create_symbol(
    library.dfcc_type.at(dfcc_typet::CAR_SET_PTR),
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

  if(goto_model.symbol_table.add(havoc_function_symbol))
  {
    log.error() << "dfcc_spec_functionst::generate_havoc_function: could not "
                   "insert symbol '"
                << havoc_function_id << "' in symbol table" << messaget::eom;
    exit(0);
  }

  // create new goto_function
  goto_functiont dummy_havoc_function;
  dummy_havoc_function.set_parameter_identifiers(havoc_code_type);
  goto_model.goto_functions.function_map[havoc_function_id].copy_from(
    dummy_havoc_function);

  // body will be filled with instructions
  auto &body =
    goto_model.goto_functions.function_map.at(havoc_function_id).body;

  // index of the CAR to havoc in the write set
  int next_idx = 0;

  // iterate on the body of the original function and emit one havoc instruction
  // per target
  Forall_goto_program_instructions(
    ins_it, goto_model.goto_functions.function_map.at(function_id).body)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        log.error().source_location = ins_it->source_location();
        log.error() << "dfcc_spec_functionst::generate_havoc_function: "
                       "function pointer calls not supported"
                    << messaget::eom;
        throw 0;
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // only process built-in functions that return assignable_t,
      // error out on any other function call
      // find the corresponding instrumentation hook
      auto hook_opt = library.get_havoc_hook(callee_id);
      if(hook_opt.has_value())
      {
        // TODO craft location for each instruction
        source_locationt location;
        auto hook = hook_opt.value();
        auto write_set_var = write_set_symbol.symbol_expr();
        code_function_callt call(
          library.dfcc_fun_symbol.at(hook).symbol_expr(),
          {write_set_var, from_integer(next_idx, size_type())});

        if(hook == dfcc_funt::WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET)
        {
          // ```
          // CALL __havoc_target = havoc_hook(set, next_idx);
          // IF !__havoc_target GOTO skip_label;
          // ASSIGN *__havoc_target = nondet(target_type);
          // skip_label: SKIP;
          // ```
          // declare a local var to store targets havoced via nondet assignment
          auto &target_type = get_target_type(ins_it->call_arguments().at(0));

          const auto &target_symbol = utils.create_symbol(
            pointer_type(target_type),
            id2string(havoc_function_id),
            "__havoc_target",
            function_symbol.location,
            function_symbol.mode,
            function_symbol.module,
            false);

          auto target_expr = target_symbol.symbol_expr();
          body.add(goto_programt::make_decl(target_expr));

          call.lhs() = target_expr;
          body.add(goto_programt::make_function_call(call, location));

          auto goto_instruction = body.add(goto_programt::make_incomplete_goto(
            utils.make_null_check_expr(write_set_var)));
          // create nondet assignment to the target
          side_effect_expr_nondett nondet(target_type, location);
          body.add(goto_programt::make_assignment(
            dereference_exprt{typecast_exprt::conditional_cast(
              target_expr, pointer_type(target_type))},
            nondet,
            location));
          auto label_instruction = body.add(goto_programt::make_skip());
          body.add(goto_programt::make_dead(target_expr));
          goto_instruction->complete_goto(label_instruction);
        }
        else if(
          hook == dfcc_funt::WRITE_SET_HAVOC_WHOLE_OBJECT ||
          hook == dfcc_funt::WRITE_SET_HAVOC_OBJECT_FROM ||
          hook == dfcc_funt::WRITE_SET_HAVOC_OBJECT_UPTO)
        {
          // ```
          // CALL havoc_hook(set, next_idx);
          // ```
          body.add(goto_programt::make_function_call(call, location));
        }
        else
        {
          UNREACHABLE;
        }
        ++next_idx;
      }
      else
      {
        INVARIANT(
          false,
          "dfcc_spec_functionst::generate_havoc_function: function calls must "
          "be inlined before calling this function");
      }
    }
    nof_targets = next_idx;
  }

  body.add(goto_programt::make_end_function());

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
    no_body.size() == 0,
    "no body warnings when inlining " + id2string(havoc_function_id));
  INVARIANT(
    missing_function.size() == 0,
    "missing function warnings when inlining " + id2string(havoc_function_id));
  INVARIANT(
    recursive_call.size() == 0,
    "recursive calls when inlining " + id2string(havoc_function_id));
  INVARIANT(
    not_enough_arguments.size() == 0,
    "not enough arguments when inlining " + id2string(havoc_function_id));

  utils.set_hide(havoc_function_id, true);

  goto_model.goto_functions.update();
}

void dfcc_spec_functionst::to_spec_assigns_function(
  const irep_idt &function_id,
  int &nof_targets)
{
  PRECONDITION(is_assignable_t_function(function_id));
  log.debug() << "->dfcc_spec_functionst::to_spec_assigns_function("
              << function_id << ")" << messaget::eom;

  // counts the number of calls to built-ins to get an over approximation
  // of the size of the set
  int next_idx = 0;

  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  // add write_set parameter
  auto &set_symbol = utils.add_parameter(
    function_id,
    "__write_set_to_fill",
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR]);

  // rewrite calls
  Forall_goto_program_instructions(ins_it, goto_function.body)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        log.error().source_location = ins_it->source_location();
        log.error()
          << "dfcc_spec_functionst::function pointer calls not supported"
          << messaget::eom;
        throw 0;
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // only process built-in functions that return assignable_t,
      // error out on any other function call
      // find the corresponding instrumentation hook
      auto hook_opt = library.get_hook(callee_id);
      if(hook_opt.has_value())
      {
        auto hook = hook_opt.value();
        // redirect the call to the hook
        ins_it->call_function() = library.dfcc_fun_symbol[hook].symbol_expr();
        // insert insertion index argument
        ins_it->call_arguments().insert(
          ins_it->call_arguments().begin(),
          from_integer(next_idx, size_type()));
        // insert write set argument
        ins_it->call_arguments().insert(
          ins_it->call_arguments().begin(), set_symbol.symbol_expr());

        // remove the is_pointer_to_pointer argument which is not used in the
        // hook
        if(hook == dfcc_funt::WRITE_SET_INSERT_ASSIGNABLE)
          ins_it->call_arguments().pop_back();

        ++next_idx;
      }
      else
      {
        INVARIANT(
          false,
          "dfcc_spec_functionst::to_spec_assigns_function: function calls must "
          "be inlined before calling this function");
      }
    }
  }

  nof_targets = next_idx;
  goto_model.goto_functions.update();

  // instrument for side-effects checking
  instrument.instrument_function(function_id);
  utils.set_hide(function_id, true);

  // print result
  auto ns = namespacet(goto_model.symbol_table);
  forall_goto_program_instructions(ins_it, goto_function.body)
  {
    goto_function.body.output_instruction(
      ns, function_id, log.debug(), *ins_it);
  }
  log.debug() << "<-dfcc_spec_functionst::to_spec_assigns_function("
              << function_id << ")" << messaget::eom;
}

void dfcc_spec_functionst::to_spec_frees_function(
  const irep_idt &function_id,
  int &nof_targets)
{
  PRECONDITION(is_freeable_t_function(function_id));
  log.debug() << "dfcc_spec_functionst::to_spec_frees_function(" << function_id
              << ")" << messaget::eom;

  // counts the number of calls to the `freeable` builtin

  int next_idx = 0;
  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  // add __dfcc_set parameter
  auto &set_symbol = utils.add_parameter(
    function_id,
    "__write_set_to_fill",
    library.dfcc_type[dfcc_typet::WRITE_SET_PTR]);

  Forall_goto_program_instructions(ins_it, goto_function.body)
  {
    if(ins_it->is_function_call())
    {
      if(ins_it->call_function().id() != ID_symbol)
      {
        log.error().source_location = ins_it->source_location();
        log.error() << "function pointer calls not supported" << messaget::eom;
        throw 0;
      }

      const irep_idt &callee_id =
        to_symbol_expr(ins_it->call_function()).get_identifier();

      // only process the built-in `freeable` function
      // error out on any other function call
      if(callee_id == CPROVER_PREFIX "freeable")
      {
        ins_it->call_function() =
          library.dfcc_fun_symbol[dfcc_funt::WRITE_SET_ADD_FREEABLE]
            .symbol_expr();
        ins_it->call_arguments().insert(
          ins_it->call_arguments().begin(), set_symbol.symbol_expr());
        ++next_idx;
      }
      else
      {
        INVARIANT(
          false,
          "dfcc_spec_functionst::to_spec_frees_function: function calls must "
          "be inlined before calling this function");
      }
    }
  }

  nof_targets = next_idx;
  goto_model.goto_functions.update();

  // instrument for side-effects checking
  instrument.instrument_function(function_id);

  auto ns = namespacet(goto_model.symbol_table);
  forall_goto_program_instructions(ins_it, goto_function.body)
  {
    goto_function.body.output_instruction(
      ns, function_id, log.debug(), *ins_it);
  }
  utils.set_hide(function_id, true);
}
