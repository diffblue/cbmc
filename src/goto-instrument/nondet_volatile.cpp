/*******************************************************************\

Module: Volatile Variables

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Volatile Variables

#include "nondet_volatile.h"

#include <util/cmdline.h>
#include <util/fresh_symbol.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_utils.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_model.h>

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
    if(!all_nondet && nondet_variables.empty() && variable_models.empty())
    {
      return;
    }

    for(auto &f : goto_model.goto_functions.function_map)
    {
      nondet_volatile(goto_model.symbol_table, f.second.body);
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
    const symbol_tablet &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void nondet_volatile_lhs(
    const symbol_tablet &symbol_table,
    exprt &expr,
    goto_programt &pre,
    goto_programt &post);

  void
  nondet_volatile(symbol_tablet &symbol_table, goto_programt &goto_program);

  const symbolt &typecheck_variable(const irep_idt &id, const namespacet &ns);

  void typecheck_model(
    const irep_idt &id,
    const symbolt &variable,
    const namespacet &ns);

  void typecheck_options(const optionst &options);

  goto_modelt &goto_model;

  // configuration obtained from command line options
  bool all_nondet;
  std::set<irep_idt> nondet_variables;
  std::map<irep_idt, irep_idt> variable_models;
};

bool nondet_volatilet::is_volatile(const namespacet &ns, const typet &src)
{
  if(src.get_bool(ID_C_volatile))
    return true;

  if(
    src.id() == ID_struct_tag || src.id() == ID_union_tag ||
    src.id() == ID_c_enum_tag)
  {
    return is_volatile(ns, ns.follow(src));
  }

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
     nondet_variables.count(to_symbol_expr(expr).get_identifier()) != 0))
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

  const irep_idt &id = to_symbol_expr(expr).get_identifier();
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
  const symbol_tablet &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  Forall_operands(it, expr)
    nondet_volatile_rhs(symbol_table, *it, pre, post);

  if(expr.id()==ID_symbol ||
     expr.id()==ID_dereference)
  {
    const namespacet ns(symbol_table);

    if(is_volatile(ns, expr.type()))
    {
      handle_volatile_expression(expr, ns, pre, post);
    }
  }
}

void nondet_volatilet::nondet_volatile_lhs(
  const symbol_tablet &symbol_table,
  exprt &expr,
  goto_programt &pre,
  goto_programt &post)
{
  if(expr.id()==ID_if)
  {
    nondet_volatile_rhs(symbol_table, to_if_expr(expr).cond(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).true_case(), pre, post);
    nondet_volatile_lhs(symbol_table, to_if_expr(expr).false_case(), pre, post);
  }
  else if(expr.id()==ID_index)
  {
    nondet_volatile_lhs(symbol_table, to_index_expr(expr).array(), pre, post);
    nondet_volatile_rhs(symbol_table, to_index_expr(expr).index(), pre, post);
  }
  else if(expr.id()==ID_member)
  {
    nondet_volatile_lhs(
      symbol_table, to_member_expr(expr).struct_op(), pre, post);
  }
  else if(expr.id()==ID_dereference)
  {
    nondet_volatile_rhs(
      symbol_table, to_dereference_expr(expr).pointer(), pre, post);
  }
}

void nondet_volatilet::nondet_volatile(
  symbol_tablet &symbol_table,
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
    }
    else if(instruction.is_function_call())
    {
      // these have arguments and a return LHS

      code_function_callt &code_function_call =
        to_code_function_call(instruction.code_nonconst());

      // do arguments
      for(exprt::operandst::iterator
          it=code_function_call.arguments().begin();
          it!=code_function_call.arguments().end();
          it++)
        nondet_volatile_rhs(symbol_table, *it, pre, post);

      // do return value
      nondet_volatile_lhs(symbol_table, code_function_call.lhs(), pre, post);
    }
    else if(instruction.has_condition())
    {
      // do condition
      exprt cond = instruction.get_condition();
      nondet_volatile_rhs(symbol_table, cond, pre, post);
      instruction.set_condition(cond);
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

void nondet_volatilet::typecheck_options(const optionst &options)
{
  PRECONDITION(!all_nondet);
  PRECONDITION(nondet_variables.empty());
  PRECONDITION(variable_models.empty());

  if(options.get_bool_option(NONDET_VOLATILE_OPT))
  {
    all_nondet = true;
    return;
  }

  const namespacet ns(goto_model.symbol_table);

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
}

void nondet_volatile(goto_modelt &goto_model, const optionst &options)
{
  nondet_volatilet nv(goto_model, options);
  nv();
}
