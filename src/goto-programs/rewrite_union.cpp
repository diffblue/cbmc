/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "rewrite_union.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>

static bool have_to_rewrite_union(const exprt &expr)
{
  if(expr.id()==ID_member)
  {
    const exprt &op=to_member_expr(expr).struct_op();

    if(op.type().id() == ID_union_tag || op.type().id() == ID_union)
      return true;
  }
  else if(expr.id()==ID_union)
    return true;

  forall_operands(it, expr)
    if(have_to_rewrite_union(*it))
      return true;

  return false;
}

// inside an address of (&x), unions can simply
// be type casts and don't have to be re-written!
void rewrite_union_address_of(exprt &expr)
{
  if(!have_to_rewrite_union(expr))
    return;

  if(expr.id()==ID_index)
  {
    rewrite_union_address_of(to_index_expr(expr).array());
    rewrite_union(to_index_expr(expr).index());
  }
  else if(expr.id()==ID_member)
    rewrite_union_address_of(to_member_expr(expr).struct_op());
  else if(expr.id()==ID_symbol)
  {
    // done!
  }
  else if(expr.id()==ID_dereference)
    rewrite_union(to_dereference_expr(expr).pointer());
}

/// We rewrite u.c for unions u into byte_extract(u, 0), and { .c = v } into
/// byte_update(NIL, 0, v)
void rewrite_union(exprt &expr)
{
  if(expr.id()==ID_address_of)
  {
    rewrite_union_address_of(to_address_of_expr(expr).object());
    return;
  }

  if(!have_to_rewrite_union(expr))
    return;

  Forall_operands(it, expr)
    rewrite_union(*it);

  if(expr.id()==ID_member)
  {
    const exprt &op=to_member_expr(expr).struct_op();

    if(op.type().id() == ID_union_tag || op.type().id() == ID_union)
    {
      exprt offset=from_integer(0, index_type());
      expr = make_byte_extract(op, offset, expr.type());
    }
  }
  else if(expr.id()==ID_union)
  {
    const union_exprt &union_expr=to_union_expr(expr);
    exprt offset=from_integer(0, index_type());
    side_effect_expr_nondett nondet(expr.type(), expr.source_location());
    expr = make_byte_update(nondet, offset, union_expr.op());
  }
}

void rewrite_union(goto_functionst::goto_functiont &goto_function)
{
  for(auto &instruction : goto_function.body.instructions)
  {
    rewrite_union(instruction.code_nonconst());

    if(instruction.has_condition())
    {
      exprt c = instruction.get_condition();
      rewrite_union(c);
      instruction.set_condition(c);
    }
  }
}

void rewrite_union(goto_functionst &goto_functions)
{
  for(auto &gf_entry : goto_functions.function_map)
    rewrite_union(gf_entry.second);
}

void rewrite_union(goto_modelt &goto_model)
{
  rewrite_union(goto_model.goto_functions);
}

/// Undo the union access -> byte_extract replacement that rewrite_union did for
/// the purpose of displaying expressions to users.
/// \param expr: expression to inspect and possibly transform
/// \param ns: namespace
/// \return True if, and only if, the expression is unmodified
static bool restore_union_rec(exprt &expr, const namespacet &ns)
{
  bool unmodified = true;

  Forall_operands(it, expr)
    unmodified &= restore_union_rec(*it, ns);

  if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    byte_extract_exprt &be = to_byte_extract_expr(expr);
    if(be.op().type().id() == ID_union || be.op().type().id() == ID_union_tag)
    {
      const union_typet &union_type = to_union_type(ns.follow(be.op().type()));

      for(const auto &comp : union_type.components())
      {
        if(be.offset().is_zero() && be.type() == comp.type())
        {
          expr = member_exprt{be.op(), comp.get_name(), be.type()};
          return false;
        }
        else if(
          comp.type().id() == ID_array || comp.type().id() == ID_struct ||
          comp.type().id() == ID_struct_tag)
        {
          optionalt<exprt> result = get_subexpression_at_offset(
            member_exprt{be.op(), comp.get_name(), comp.type()},
            be.offset(),
            be.type(),
            ns);
          if(result.has_value())
          {
            expr = *result;
            return false;
          }
        }
      }
    }
  }

  return unmodified;
}

/// Undo the union access -> byte_extract replacement that rewrite_union did for
/// the purpose of displaying expressions to users.
/// \param expr: expression to inspect and possibly transform
/// \param ns: namespace
void restore_union(exprt &expr, const namespacet &ns)
{
  exprt tmp = expr;

  if(!restore_union_rec(tmp, ns))
    expr.swap(tmp);
}
