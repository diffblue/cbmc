/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "rewrite_union.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/byte_operators.h>

#include <goto-programs/goto_model.h>

#include <util/c_types.h>

static bool have_to_rewrite_union(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_member)
  {
    const exprt &op=to_member_expr(expr).struct_op();
    const typet &op_type=ns.follow(op.type());

    if(op_type.id()==ID_union)
      return true;
  }
  else if(expr.id()==ID_union)
    return true;

  forall_operands(it, expr)
    if(have_to_rewrite_union(*it, ns))
      return true;

  return false;
}

// inside an address of (&x), unions can simply
// be type casts and don't have to be re-written!
void rewrite_union_address_of(
  exprt &expr,
  const namespacet &ns)
{
  if(!have_to_rewrite_union(expr, ns))
    return;

  if(expr.id()==ID_index)
  {
    rewrite_union_address_of(to_index_expr(expr).array(), ns);
    rewrite_union(to_index_expr(expr).index(), ns);
  }
  else if(expr.id()==ID_member)
    rewrite_union_address_of(to_member_expr(expr).struct_op(), ns);
  else if(expr.id()==ID_symbol)
  {
    // done!
  }
  else if(expr.id()==ID_dereference)
    rewrite_union(to_dereference_expr(expr).pointer(), ns);
}

/// We rewrite u.c for unions u into byte_extract(u, 0), and { .c = v } into
/// byte_update(NIL, 0, v)
void rewrite_union(
  exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_address_of)
  {
    rewrite_union_address_of(to_address_of_expr(expr).object(), ns);
    return;
  }

  if(!have_to_rewrite_union(expr, ns))
    return;

  Forall_operands(it, expr)
    rewrite_union(*it, ns);

  if(expr.id()==ID_member)
  {
    const exprt &op=to_member_expr(expr).struct_op();
    const typet &op_type=ns.follow(op.type());

    if(op_type.id()==ID_union)
    {
      exprt offset=from_integer(0, index_type());
      byte_extract_exprt tmp(byte_extract_id(), op, offset, expr.type());
      expr=tmp;
    }
  }
  else if(expr.id()==ID_union)
  {
    const union_exprt &union_expr=to_union_expr(expr);
    exprt offset=from_integer(0, index_type());
    side_effect_expr_nondett nondet(expr.type());
    byte_update_exprt tmp(
      byte_update_id(), nondet, offset, union_expr.op());
    expr=tmp;
  }
}

static void rewrite_union(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    rewrite_union(it->code, ns);
    rewrite_union(it->guard, ns);
  }
}

void rewrite_union(
  goto_functionst::goto_functiont &goto_function,
  const symbol_tablet &symbol_table)
{
  rewrite_union(goto_function, namespacet(symbol_table));
}

void rewrite_union(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(it, goto_functions)
    rewrite_union(it->second, ns);
}

void rewrite_union(goto_modelt &goto_model)
{
  rewrite_union(
    goto_model.goto_functions, namespacet(goto_model.symbol_table));
}
