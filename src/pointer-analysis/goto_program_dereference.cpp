/*******************************************************************\

Module: Dereferencing Operations on GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dereferencing Operations on GOTO Programs

#include "goto_program_dereference.h"

#include <util/expr_util.h>
#include <util/options.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_model.h>

/// \param expr: expression to check
/// \return pointer to appropriate failed symbol for \p expr, or nullptr if none
const symbolt *
goto_program_dereferencet::get_or_create_failed_symbol(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    if(expr.get_bool(ID_C_invalid_object))
      return nullptr;

    const symbolt &ptr_symbol = ns.lookup(to_symbol_expr(expr));

    const irep_idt &failed_symbol = ptr_symbol.type.get(ID_C_failed_symbol);

    if(failed_symbol.empty())
      return nullptr;

    const symbolt *symbol = nullptr;
    ns.lookup(failed_symbol, symbol);
    return symbol;
  }

  return nullptr;
}

/// Turn subexpression of `expr` of the form `&*p` into p
/// and use `dereference` on subexpressions of the form `*p`
/// \param expr: expression in which to remove dereferences
void goto_program_dereferencet::dereference_rec(exprt &expr)
{
  if(!has_subexpr(expr, ID_dereference))
    return;

  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(!expr.is_boolean())
      throw expr.id_string()+" must be Boolean, but got "+
            expr.pretty();

    for(auto &op : expr.operands())
    {
      if(!op.is_boolean())
        throw expr.id_string()+" takes Boolean operands only, but got "+
              op.pretty();

      if(has_subexpr(op, ID_dereference))
        dereference_rec(op);
    }
    return;
  }
  else if(expr.id()==ID_if)
  {
    auto &if_expr = to_if_expr(expr);

    if(!if_expr.cond().is_boolean())
    {
      std::string msg = "first argument of if must be boolean, but got " +
                        if_expr.cond().pretty();
      throw msg;
    }

    dereference_rec(if_expr.cond());

    bool o1 = has_subexpr(if_expr.true_case(), ID_dereference);
    bool o2 = has_subexpr(if_expr.false_case(), ID_dereference);

    if(o1)
      dereference_rec(if_expr.true_case());

    if(o2)
      dereference_rec(if_expr.false_case());

    return;
  }

  if(expr.id() == ID_address_of)
  {
    // turn &*p to p
    // this has *no* side effect!

    if(to_address_of_expr(expr).object().id() == ID_dereference)
      expr = typecast_exprt::conditional_cast(
        to_dereference_expr(to_address_of_expr(expr).object()).pointer(),
        expr.type());
  }

  Forall_operands(it, expr)
    dereference_rec(*it);

  if(expr.id()==ID_dereference)
  {
    expr = dereference.dereference(to_dereference_expr(expr).pointer());
  }
  else if(expr.id()==ID_index)
  {
    // this is old stuff and will go away

    if(to_index_expr(expr).array().type().id() == ID_pointer)
    {
      exprt tmp1(ID_plus, to_index_expr(expr).array().type());
      tmp1.operands().swap(expr.operands());

      exprt tmp2 = dereference.dereference(tmp1);
      tmp2.swap(expr);
    }
  }
}

/// Gets the value set corresponding to the current target and
/// expression \p expr.
/// \param expr: an expression
/// \return the value set
std::vector<exprt>
goto_program_dereferencet::get_value_set(const exprt &expr) const
{
  return value_sets.get_values(current_function, current_target, expr);
}

/// Remove dereference expressions contained in `expr`.
/// \param expr: an expression
/// \param checks_only: when true, execute the substitution on a copy of expr
///   so that `expr` stays unchanged. In that case the only observable effect
///   is whether an exception would be thrown.
void goto_program_dereferencet::dereference_expr(
  exprt &expr,
  const bool checks_only)
{
  if(checks_only)
  {
    exprt tmp(expr);
    dereference_rec(tmp);
  }
  else
    dereference_rec(expr);
}

void goto_program_dereferencet::dereference_program(
  goto_programt &goto_program,
  bool checks_only)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    new_code.clear();
    dereference_instruction(it, checks_only);

    // insert new instructions
    while(!new_code.instructions.empty())
    {
      goto_program.insert_before_swap(it, new_code.instructions.front());
      new_code.instructions.pop_front();
      it++;
    }
  }
}

void goto_program_dereferencet::dereference_program(
  goto_functionst &goto_functions,
  bool checks_only)
{
  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    dereference_program(it->second.body, checks_only);
}

/// Remove dereference from expressions contained in the instruction at
/// `target`. If `check_only` is true, the dereferencing is performed on copies
/// of the expressions, in that case the only observable effect is whether an
/// exception would be thrown.
void goto_program_dereferencet::dereference_instruction(
  goto_programt::targett target,
  bool checks_only)
{
  current_target=target;
  goto_programt::instructiont &i=*target;

  if(i.has_condition())
    dereference_expr(i.condition_nonconst(), checks_only);

  if(i.is_assign())
  {
    dereference_expr(i.assign_lhs_nonconst(), checks_only);
    dereference_expr(i.assign_rhs_nonconst(), checks_only);
  }
  else if(i.is_function_call())
  {
    if(as_const(i).call_lhs().is_not_nil())
      dereference_expr(i.call_lhs(), checks_only);

    dereference_expr(i.call_function(), checks_only);

    for(auto &arg : i.call_arguments())
      dereference_expr(arg, checks_only);
  }
  else if(i.is_set_return_value())
  {
    dereference_expr(i.return_value(), checks_only);
  }
  else if(i.is_other())
  {
    auto code = i.get_other();
    const irep_idt &statement = code.get_statement();

    if(statement==ID_expression)
    {
      if(code.operands().size() != 1)
        throw "expression expects one operand";

      dereference_expr(to_code_expression(code).expression(), checks_only);
    }
    else if(statement==ID_printf)
    {
      for(auto &op : code.operands())
        dereference_expr(op, checks_only);
    }

    i.set_other(code);
  }
}

/// Set the current target to `target` and remove derefence from expr.
void goto_program_dereferencet::dereference_expression(
  const irep_idt &function_id,
  goto_programt::const_targett target,
  exprt &expr)
{
  current_function = function_id;
  current_target=target;
  dereference_expr(expr, false);
}

/// Remove dereferences in all expressions contained in the program
/// `goto_model`. `value_sets` is used to determine to what objects the pointers
/// may be pointing to.
void remove_pointers(
  goto_modelt &goto_model,
  value_setst &value_sets)
{
  namespacet ns(goto_model.symbol_table);

  optionst options;

  goto_program_dereferencet
    goto_program_dereference(
      ns, goto_model.symbol_table, options, value_sets);

  for(auto &gf_entry : goto_model.goto_functions.function_map)
    goto_program_dereference.dereference_program(gf_entry.second.body);
}

/// Remove dereferences in `expr` using `value_sets` to determine to what
/// objects the pointers may be pointing to.
void dereference(
  const irep_idt &function_id,
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &ns,
  value_setst &value_sets)
{
  optionst options;
  symbol_tablet new_symbol_table;
  goto_program_dereferencet
    goto_program_dereference(ns, new_symbol_table, options, value_sets);
  goto_program_dereference.dereference_expression(function_id, target, expr);
}
