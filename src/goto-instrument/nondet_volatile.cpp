/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Volatile Variables

#include "nondet_volatile.h"

#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/fresh_symbol.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <goto-programs/goto_instruction_code.h>
#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

#include "wmm/fence.h"

class nondet_volatilet
{
public:
  nondet_volatilet(goto_modelt &goto_model, const optionst &options)
    : goto_model(goto_model), all_nondet(false)
  {
    typecheck_options(options);
  }

  void operator()()
  {
    if(
      !all_nondet && nondet_variables.empty() && variable_models.empty() &&
      write_models.empty())
    {
      return;
    }

    for(auto &f : goto_model.goto_functions.function_map)
    {
      nondet_volatile(goto_model.symbol_table, f.first, f.second.body);

      if(weak_mmio)
      {
        instrument_posted_writes(
          goto_model.symbol_table, f.first, f.second.body);
      }
    }

    goto_model.goto_functions.update();
  }

private:
  static bool is_volatile(const namespacet &ns, const typet &src);

  void handle_volatile_expression(
    exprt &expr,
    const namespacet &ns,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile_rhs(
    const symbol_table_baset &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile_lhs(
    const symbol_table_baset &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile(
    symbol_table_baset &symbol_table,
    const irep_idt &function_id,
    goto_programt &goto_program);

  /// Is a write to \p lhs modelled as a device side effect (so that it should
  /// be preserved as an observable event)? True for any volatile lvalue in
  /// --nondet-volatile mode, and for the specifically-selected variables in
  /// the scoped (--nondet-volatile-variable / --nondet-volatile-model) modes.
  bool is_modeled_volatile_write(const exprt &lhs, const namespacet &ns) const;

  /// Instrument a write to a volatile lvalue as an observable device side
  /// effect: route it to the configured write model, or otherwise emit an
  /// OUTPUT of the written value so the store is not sliced away as dead.
  void observe_volatile_write(
    const goto_programt::instructiont &instruction,
    const irep_idt &function_id,
    const namespacet &ns,
    goto_programt &post);

  /// Is \p instruction a full memory barrier (a fence, or a call to
  /// __sync_synchronize)? Used as a flush point for the weak MMIO model.
  static bool is_barrier(
    const goto_programt::instructiont &instruction,
    const namespacet &ns);

  /// Weak MMIO model (--mmio-weak): make writes to write-modelled registers
  /// "posted". Each such write is non-deterministically either committed
  /// immediately (the write model is called at the write) or deferred until the
  /// next barrier or the end of the function. A later write to a different
  /// register may then be observed before an earlier posted one, exposing
  /// missing-barrier ordering bugs, while a barrier forces in-order
  /// observation.
  void instrument_posted_writes(
    symbol_table_baset &symbol_table,
    const irep_idt &function_id,
    goto_programt &goto_program);

  const symbolt &typecheck_variable(const irep_idt &id, const namespacet &ns);

  void typecheck_model(
    const irep_idt &id,
    const symbolt &variable,
    const namespacet &ns);

  void typecheck_write_model(
    const irep_idt &id,
    const symbolt &variable,
    const namespacet &ns);

  void typecheck_options(const optionst &options);

  goto_modelt &goto_model;

  // configuration obtained from command line options
  bool all_nondet;
  std::set<irep_idt> nondet_variables;
  std::map<irep_idt, irep_idt> variable_models;
  std::map<irep_idt, irep_idt> write_models;
  bool weak_mmio = false;
};

bool nondet_volatilet::is_volatile(const namespacet &ns, const typet &src)
{
  if(src.get_bool(ID_C_volatile))
    return true;

  if(auto struct_tag = type_try_dynamic_cast<struct_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*struct_tag));
  else if(auto union_tag = type_try_dynamic_cast<union_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*union_tag));
  else if(auto enum_tag = type_try_dynamic_cast<c_enum_tag_typet>(src))
    return is_volatile(ns, ns.follow_tag(*enum_tag));
  else
    return false;
}

void nondet_volatilet::handle_volatile_expression(
  exprt &expr,
  const namespacet &ns,
  goto_programt &pre,
  goto_programt &post)
{
  // Check if we should replace the variable by a nondet expression
  if(
    all_nondet ||
    (expr.id() == ID_symbol &&
     nondet_variables.count(to_symbol_expr(expr).identifier()) != 0))
  {
    typet t = expr.type();
    t.remove(ID_C_volatile);

    side_effect_expr_nondett nondet_expr(t, expr.source_location());
    expr.swap(nondet_expr);

    return;
  }

  // Now check if we should replace the variable by a model

  if(expr.id() != ID_symbol)
  {
    return;
  }

  const irep_idt &id = to_symbol_expr(expr).identifier();
  const auto &it = variable_models.find(id);

  if(it == variable_models.end())
  {
    return;
  }

  const auto &model_symbol = ns.lookup(it->second);

  const auto &new_variable = get_fresh_aux_symbol(
                               to_code_type(model_symbol.type).return_type(),
                               "",
                               "modelled_volatile",
                               source_locationt(),
                               ID_C,
                               goto_model.symbol_table)
                               .symbol_expr();

  pre.instructions.push_back(goto_programt::make_decl(new_variable));

  code_function_callt call(new_variable, model_symbol.symbol_expr(), {});
  pre.instructions.push_back(goto_programt::make_function_call(call));

  post.instructions.push_back(goto_programt::make_dead(new_variable));

  expr = new_variable;
}

void nondet_volatilet::nondet_volatile_rhs(
  const symbol_table_baset &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  Forall_operands(it, expr)
    nondet_volatile_rhs(symbol_table, *it, pre, post);

  if(expr.id() == ID_symbol || expr.id() == ID_dereference)
  {
    const namespacet ns(symbol_table);

    if(is_volatile(ns, expr.type()))
    {
      handle_volatile_expression(expr, ns, pre, post);
    }
  }
}

void nondet_volatilet::nondet_volatile_lhs(
  const symbol_table_baset &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  if(expr.id() == ID_if)
  {
    nondet_volatile_rhs(symbol_table, to_if_expr(expr).cond(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).true_case(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).false_case(), pre, post);
  }
  else if(expr.id() == ID_index)
  {
    nondet_volatile_lhs(symbol_table, to_index_expr(expr).array(), pre, post);
    nondet_volatile_rhs(symbol_table, to_index_expr(expr).index(), pre, post);
  }
  else if(expr.id() == ID_member)
  {
    nondet_volatile_lhs(
      symbol_table, to_member_expr(expr).struct_op(), pre, post);
  }
  else if(expr.id() == ID_dereference)
  {
    nondet_volatile_rhs(
      symbol_table, to_dereference_expr(expr).pointer(), pre, post);
  }
}

bool nondet_volatilet::is_modeled_volatile_write(
  const exprt &lhs,
  const namespacet &ns) const
{
  if(all_nondet)
    return is_volatile(ns, lhs.type());

  if(lhs.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(lhs).identifier();
    return nondet_variables.count(id) != 0 || variable_models.count(id) != 0;
  }

  return false;
}

void nondet_volatilet::observe_volatile_write(
  const goto_programt::instructiont &instruction,
  const irep_idt &function_id,
  const namespacet &ns,
  goto_programt &post)
{
  // The zero-initialisation of globals in the CPROVER initialisation function
  // is a language-level artefact, not an action on the device, so it is not
  // treated as an observable device write.
  if(function_id == INITIALIZE_FUNCTION)
    return;

  const exprt &lhs = instruction.assign_lhs();

  // A write model configured for this register observes (and can assert on)
  // the written value; it supersedes the default observable output.
  if(lhs.id() == ID_symbol)
  {
    const auto it = write_models.find(to_symbol_expr(lhs).identifier());

    if(it != write_models.end())
    {
      // Under the weak MMIO model the write model is called by the posted-write
      // instrumentation (possibly reordered); here we only need to suppress the
      // default observable OUTPUT for a write-modelled register.
      if(!weak_mmio)
      {
        const symbolt &model_symbol = ns.lookup(it->second);

        post.instructions.push_back(goto_programt::make_function_call(
          code_function_callt{
            model_symbol.symbol_expr(), {instruction.assign_rhs()}},
          instruction.source_location()));
      }

      return;
    }
  }

  // Otherwise, if this register is modelled as a device, a write to it is an
  // observable side effect: it acts on the device rather than merely updating
  // storage the program later reads. When volatile reads are modelled
  // non-deterministically the written value is never read back, so without
  // this the store would be sliced away as dead. Emit an OUTPUT of the written
  // value so the write is preserved and appears in counterexample traces.
  if(is_modeled_volatile_write(lhs, ns))
  {
    post.instructions.push_back(goto_programt::make_other(
      code_outputt{
        "volatile-write",
        instruction.assign_rhs(),
        instruction.source_location()},
      instruction.source_location()));
  }
}

bool nondet_volatilet::is_barrier(
  const goto_programt::instructiont &instruction,
  const namespacet &ns)
{
  // a full fence, e.g. __CPROVER_fence with all of WW/WR/RW/RR set
  if(is_fence(instruction, ns))
    return true;

  // a call to __sync_synchronize (the gcc/Linux full memory barrier)
  if(instruction.is_function_call())
  {
    const exprt &function = instruction.call_function();
    if(function.id() == ID_symbol)
    {
      return ns.lookup(to_symbol_expr(function)).base_name ==
             "__sync_synchronize";
    }
  }

  return false;
}

void nondet_volatilet::instrument_posted_writes(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  goto_programt &goto_program)
{
  const namespacet ns(symbol_table);

  // collect the write-modelled registers written in this function
  std::map<irep_idt, irep_idt> registers;
  for(const auto &instruction : goto_program.instructions)
  {
    if(instruction.is_assign() && instruction.assign_lhs().id() == ID_symbol)
    {
      const irep_idt &id =
        to_symbol_expr(instruction.assign_lhs()).identifier();
      const auto it = write_models.find(id);
      if(it != write_models.end())
        registers.emplace(id, it->second);
    }
  }

  if(registers.empty())
    return;

  // A pending posted write per register: a validity flag and the value.
  struct posted_writet
  {
    symbol_exprt valid;
    symbol_exprt value;
    irep_idt model;
  };
  std::map<irep_idt, posted_writet> posted;

  for(const auto &r : registers)
  {
    const symbolt &register_symbol = ns.lookup(r.first);
    const symbol_exprt valid = get_fresh_aux_symbol(
                                 bool_typet{},
                                 id2string(function_id),
                                 "mmio_posted_valid",
                                 source_locationt{},
                                 ID_C,
                                 symbol_table)
                                 .symbol_expr();
    const symbol_exprt value = get_fresh_aux_symbol(
                                 register_symbol.type,
                                 id2string(function_id),
                                 "mmio_posted_value",
                                 source_locationt{},
                                 ID_C,
                                 symbol_table)
                                 .symbol_expr();
    posted.emplace(r.first, posted_writet{valid, value, r.second});
  }

  // append "if(<valid>) { <model>(<value>); [<valid> = false;] }" to dest
  const auto emit_flush = [&ns](
                            goto_programt &dest,
                            const posted_writet &p,
                            const source_locationt &loc,
                            bool clear_valid)
  {
    auto guard =
      dest.add(goto_programt::make_incomplete_goto(not_exprt{p.valid}, loc));
    dest.add(goto_programt::make_function_call(
      code_function_callt{ns.lookup(p.model).symbol_expr(), {p.value}}, loc));
    if(clear_valid)
      dest.add(goto_programt::make_assignment(p.valid, false_exprt{}, loc));
    auto label = dest.add(goto_programt::make_skip(loc));
    guard->complete_goto(label);
  };

  // declare and initialise the per-register buffers at the function's entry
  {
    goto_programt declarations;
    for(const auto &p : posted)
    {
      declarations.add(goto_programt::make_decl(p.second.valid));
      declarations.add(goto_programt::make_decl(p.second.value));
      declarations.add(
        goto_programt::make_assignment(p.second.valid, false_exprt{}));
    }
    goto_program.destructive_insert(
      goto_program.instructions.begin(), declarations);
  }

  // transform writes and flush at barriers
  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    if(it->is_assign() && it->assign_lhs().id() == ID_symbol)
    {
      const auto p_it =
        posted.find(to_symbol_expr(it->assign_lhs()).identifier());

      if(p_it != posted.end())
      {
        const posted_writet &p = p_it->second;
        const source_locationt loc = it->source_location();

        // buffer the written value, then non-deterministically either post it
        // (skip the call, deferring it) or commit it now (call the model)
        goto_programt fragment;
        fragment.add(
          goto_programt::make_assignment(p.value, it->assign_rhs(), loc));
        fragment.add(goto_programt::make_assignment(
          p.valid, side_effect_expr_nondett{bool_typet{}, loc}, loc));
        auto guard =
          fragment.add(goto_programt::make_incomplete_goto(p.valid, loc));
        fragment.add(goto_programt::make_function_call(
          code_function_callt{ns.lookup(p.model).symbol_expr(), {p.value}},
          loc));
        auto label = fragment.add(goto_programt::make_skip(loc));
        guard->complete_goto(label);

        goto_program.destructive_insert(std::next(it), fragment);
      }
    }
    else if(is_barrier(*it, ns))
    {
      const source_locationt loc = it->source_location();
      goto_programt fragment;
      for(const auto &p : posted)
        emit_flush(fragment, p.second, loc, true);
      goto_program.destructive_insert(std::next(it), fragment);
    }
  }

  // flush any still-posted writes and release the buffers at function exit
  auto end = std::prev(goto_program.instructions.end());
  const source_locationt loc = end->source_location();
  goto_programt epilogue;
  for(const auto &p : posted)
    emit_flush(epilogue, p.second, loc, false);
  for(const auto &p : posted)
  {
    epilogue.add(goto_programt::make_dead(p.second.value, loc));
    epilogue.add(goto_programt::make_dead(p.second.valid, loc));
  }
  goto_program.destructive_insert(end, epilogue);
}

void nondet_volatilet::nondet_volatile(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);

  for(auto i_it = goto_program.instructions.begin();
      i_it != goto_program.instructions.end();
      i_it++)
  {
    goto_programt pre;
    goto_programt post;

    goto_programt::instructiont &instruction = *i_it;

    if(instruction.is_assign())
    {
      nondet_volatile_rhs(
        symbol_table, instruction.assign_rhs_nonconst(), pre, post);
      nondet_volatile_lhs(
        symbol_table, instruction.assign_lhs_nonconst(), pre, post);

      observe_volatile_write(instruction, function_id, ns, post);
    }
    else if(instruction.is_function_call())
    {
      // these have arguments and a return LHS

      code_function_callt &code_function_call =
        to_code_function_call(instruction.code_nonconst());

      // do arguments
      for(exprt::operandst::iterator it =
            code_function_call.arguments().begin();
          it != code_function_call.arguments().end();
          it++)
        nondet_volatile_rhs(symbol_table, *it, pre, post);

      // do return value
      nondet_volatile_lhs(symbol_table, code_function_call.lhs(), pre, post);
    }
    else if(instruction.has_condition())
    {
      // do condition
      nondet_volatile_rhs(
        symbol_table, instruction.condition_nonconst(), pre, post);
    }

    const auto pre_size = pre.instructions.size();
    goto_program.insert_before_swap(i_it, pre);
    std::advance(i_it, pre_size);

    const auto post_size = post.instructions.size();
    goto_program.destructive_insert(std::next(i_it), post);
    std::advance(i_it, post_size);
  }
}

const symbolt &
nondet_volatilet::typecheck_variable(const irep_idt &id, const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given symbol `" + id2string(id) + "` not found in symbol table",
      "--" NONDET_VOLATILE_VARIABLE_OPT);
  }

  if(!symbol->is_static_lifetime || !symbol->type.get_bool(ID_C_volatile))
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) +
        "` does not represent a volatile variable "
        "with static lifetime",
      "--" NONDET_VOLATILE_VARIABLE_OPT);
  }

  INVARIANT(!symbol->is_type, "symbol must not represent a type");

  INVARIANT(!symbol->is_function(), "symbol must not represent a function");

  return *symbol;
}

void nondet_volatilet::typecheck_model(
  const irep_idt &id,
  const symbolt &variable,
  const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given model name " + id2string(id) + " not found in symbol table",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(!symbol->is_function())
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) + "` is not a function",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  const auto &code_type = to_code_type(symbol->type);

  if(variable.type != code_type.return_type())
  {
    throw invalid_command_line_argument_exceptiont(
      "return type of model `" + id2string(id) +
        "` is not compatible with the "
        "type of the modelled variable " +
        id2string(variable.name),
      "--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(!code_type.parameters().empty())
  {
    throw invalid_command_line_argument_exceptiont(
      "model `" + id2string(id) + "` must not take parameters ",
      "--" NONDET_VOLATILE_MODEL_OPT);
  }
}

void nondet_volatilet::typecheck_write_model(
  const irep_idt &id,
  const symbolt &variable,
  const namespacet &ns)
{
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
  {
    throw invalid_command_line_argument_exceptiont(
      "given write model name " + id2string(id) + " not found in symbol table",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(!symbol->is_function())
  {
    throw invalid_command_line_argument_exceptiont(
      "symbol `" + id2string(id) + "` is not a function",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  const auto &code_type = to_code_type(symbol->type);

  if(code_type.return_type().id() != ID_empty)
  {
    throw invalid_command_line_argument_exceptiont(
      "write model `" + id2string(id) + "` must return void",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(code_type.parameters().size() != 1)
  {
    throw invalid_command_line_argument_exceptiont(
      "write model `" + id2string(id) +
        "` must take exactly one parameter (the written value)",
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }

  if(variable.type != code_type.parameters().front().type())
  {
    throw invalid_command_line_argument_exceptiont(
      "parameter type of write model `" + id2string(id) +
        "` is not compatible with the type of the modelled variable " +
        id2string(variable.name),
      "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
  }
}

void nondet_volatilet::typecheck_options(const optionst &options)
{
  PRECONDITION(!all_nondet);
  PRECONDITION(nondet_variables.empty());
  PRECONDITION(variable_models.empty());
  PRECONDITION(write_models.empty());

  const namespacet ns(goto_model.symbol_table);

  // the weak MMIO model is independent of the read-side mode
  if(options.get_bool_option(MMIO_WEAK_OPT))
    weak_mmio = true;

  // Write models are independent of the read-side mode and may be combined
  // with any of them (including --nondet-volatile), so they are processed
  // before the read-side options.
  if(options.is_set(NONDET_VOLATILE_WRITE_MODEL_OPT))
  {
    const auto &model_list =
      options.get_list_option(NONDET_VOLATILE_WRITE_MODEL_OPT);

    for(const auto &s : model_list)
    {
      std::string variable;
      std::string model;

      try
      {
        split_string(s, ':', variable, model, true);
      }
      catch(const deserialization_exceptiont &)
      {
        throw invalid_command_line_argument_exceptiont(
          "cannot split argument `" + s + "` into variable name and model name",
          "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
      }

      const auto &variable_symbol = typecheck_variable(variable, ns);

      typecheck_write_model(model, variable_symbol, ns);

      const auto p = write_models.insert(std::make_pair(variable, model));

      if(!p.second && p.first->second != model)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting write models for variable `" + variable + "`",
          "--" NONDET_VOLATILE_WRITE_MODEL_OPT);
      }
    }
  }

  if(options.get_bool_option(NONDET_VOLATILE_OPT))
  {
    all_nondet = true;
    return;
  }

  if(options.is_set(NONDET_VOLATILE_VARIABLE_OPT))
  {
    const auto &variable_list =
      options.get_list_option(NONDET_VOLATILE_VARIABLE_OPT);

    nondet_variables.insert(variable_list.begin(), variable_list.end());

    for(const auto &id : nondet_variables)
    {
      typecheck_variable(id, ns);
    }
  }

  if(options.is_set(NONDET_VOLATILE_MODEL_OPT))
  {
    const auto &model_list = options.get_list_option(NONDET_VOLATILE_MODEL_OPT);

    for(const auto &s : model_list)
    {
      std::string variable;
      std::string model;

      try
      {
        split_string(s, ':', variable, model, true);
      }
      catch(const deserialization_exceptiont &e)
      {
        throw invalid_command_line_argument_exceptiont(
          "cannot split argument `" + s + "` into variable name and model name",
          "--" NONDET_VOLATILE_MODEL_OPT);
      }

      const auto &variable_symbol = typecheck_variable(variable, ns);

      if(nondet_variables.count(variable) != 0)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting options for variable `" + variable + "`",
          "--" NONDET_VOLATILE_VARIABLE_OPT "/--" NONDET_VOLATILE_MODEL_OPT);
      }

      typecheck_model(model, variable_symbol, ns);

      const auto p = variable_models.insert(std::make_pair(variable, model));

      if(!p.second && p.first->second != model)
      {
        throw invalid_command_line_argument_exceptiont(
          "conflicting models for variable `" + variable + "`",
          "--" NONDET_VOLATILE_MODEL_OPT);
      }
    }
  }
}

void parse_nondet_volatile_options(const cmdlinet &cmdline, optionst &options)
{
  PRECONDITION(!options.is_set(NONDET_VOLATILE_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_VARIABLE_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_MODEL_OPT));
  PRECONDITION(!options.is_set(NONDET_VOLATILE_WRITE_MODEL_OPT));
  PRECONDITION(!options.is_set(MMIO_WEAK_OPT));

  const bool nondet_volatile_opt = cmdline.isset(NONDET_VOLATILE_OPT);
  const bool nondet_volatile_variable_opt =
    cmdline.isset(NONDET_VOLATILE_VARIABLE_OPT);
  const bool nondet_volatile_model_opt =
    cmdline.isset(NONDET_VOLATILE_MODEL_OPT);

  if(
    nondet_volatile_opt &&
    (nondet_volatile_variable_opt || nondet_volatile_model_opt))
  {
    throw invalid_command_line_argument_exceptiont(
      "--" NONDET_VOLATILE_OPT
      " cannot be used with --" NONDET_VOLATILE_VARIABLE_OPT
      " or --" NONDET_VOLATILE_MODEL_OPT,
      "--" NONDET_VOLATILE_OPT "/--" NONDET_VOLATILE_VARIABLE_OPT
      "/--" NONDET_VOLATILE_MODEL_OPT);
  }

  if(nondet_volatile_opt)
  {
    options.set_option(NONDET_VOLATILE_OPT, true);
  }
  else
  {
    if(nondet_volatile_variable_opt)
    {
      options.set_option(
        NONDET_VOLATILE_VARIABLE_OPT,
        cmdline.get_values(NONDET_VOLATILE_VARIABLE_OPT));
    }

    if(nondet_volatile_model_opt)
    {
      options.set_option(
        NONDET_VOLATILE_MODEL_OPT,
        cmdline.get_values(NONDET_VOLATILE_MODEL_OPT));
    }
  }

  // Write models are independent of the (mutually-exclusive) read-side modes
  // and may be combined with any of them.
  if(cmdline.isset(NONDET_VOLATILE_WRITE_MODEL_OPT))
  {
    options.set_option(
      NONDET_VOLATILE_WRITE_MODEL_OPT,
      cmdline.get_values(NONDET_VOLATILE_WRITE_MODEL_OPT));
  }

  // The weak MMIO model is likewise independent of the read-side mode.
  if(cmdline.isset(MMIO_WEAK_OPT))
  {
    options.set_option(MMIO_WEAK_OPT, true);
  }
}

void nondet_volatile(goto_modelt &goto_model, const optionst &options)
{
  nondet_volatilet nv(goto_model, options);
  nv();
}
