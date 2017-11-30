/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/base_type.h>

#include <util/c_types.h>

void goto_symext::process_array_expr_rec(
  exprt &expr,
  const typet &type) const
{
  if(expr.id()==ID_if)
  {
    if_exprt &if_expr=to_if_expr(expr);
    process_array_expr_rec(if_expr.true_case(), type);
    process_array_expr_rec(if_expr.false_case(), type);
  }
  else if(expr.id()==ID_index)
  {
    // strip index
    index_exprt &index_expr=to_index_expr(expr);
    exprt tmp=index_expr.array();
    expr.swap(tmp);
  }
  else if(expr.id()==ID_typecast)
  {
    // strip
    exprt tmp=to_typecast_expr(expr).op0();
    expr.swap(tmp);
    process_array_expr_rec(expr, type);
  }
  else if(expr.id()==ID_address_of)
  {
    // strip
    exprt tmp=to_address_of_expr(expr).op0();
    expr.swap(tmp);
    process_array_expr_rec(expr, type);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    // pick the root object
    exprt tmp=to_byte_extract_expr(expr).op();
    expr.swap(tmp);
    process_array_expr_rec(expr, type);
  }
  else if(expr.id()==ID_symbol &&
          expr.get_bool(ID_C_SSA_symbol) &&
          to_ssa_expr(expr).get_original_expr().id()==ID_index)
  {
    const ssa_exprt &ssa=to_ssa_expr(expr);
    const index_exprt &index_expr=to_index_expr(ssa.get_original_expr());
    exprt tmp=index_expr.array();
    expr.swap(tmp);
  }
  else
  {
    Forall_operands(it, expr)
    {
      typet t=it->type();
      process_array_expr_rec(*it, t);
    }
  }

  if(!base_type_eq(expr.type(), type, ns))
  {
    byte_extract_exprt be(byte_extract_id());
    be.type()=type;
    be.op()=expr;
    be.offset()=from_integer(0, index_type());

    expr.swap(be);
  }
}

void goto_symext::process_array_expr(exprt &expr)
{
  // This may change the type of the expression!

  if(expr.id()==ID_if)
  {
    if_exprt &if_expr=to_if_expr(expr);
    process_array_expr(if_expr.true_case());

    process_array_expr_rec(if_expr.false_case(),
                           if_expr.true_case().type());

    if_expr.type()=if_expr.true_case().type();
  }
  else if(expr.id()==ID_index)
  {
    // strip index
    index_exprt &index_expr=to_index_expr(expr);
    exprt tmp=index_expr.array();
    expr.swap(tmp);
  }
  else if(expr.id()==ID_typecast)
  {
    // strip
    exprt tmp=to_typecast_expr(expr).op0();
    expr.swap(tmp);
    process_array_expr(expr);
  }
  else if(expr.id()==ID_address_of)
  {
    // strip
    exprt tmp=to_address_of_expr(expr).op0();
    expr.swap(tmp);
    process_array_expr(expr);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    // pick the root object
    exprt tmp=to_byte_extract_expr(expr).op();
    expr.swap(tmp);
    process_array_expr(expr);
  }
  else if(expr.id()==ID_symbol &&
          expr.get_bool(ID_C_SSA_symbol) &&
          to_ssa_expr(expr).get_original_expr().id()==ID_index)
  {
    const ssa_exprt &ssa=to_ssa_expr(expr);
    const index_exprt &index_expr=to_index_expr(ssa.get_original_expr());
    exprt tmp=index_expr.array();
    expr.swap(tmp);
  }
  else
    Forall_operands(it, expr)
      process_array_expr(*it);
}

void goto_symext::replace_array_equal(exprt &expr)
{
  if(expr.id()==ID_array_equal)
  {
    assert(expr.operands().size()==2);

    // we expect two index expressions
    process_array_expr(expr.op0());
    process_array_expr(expr.op1());

    // type checking
    if(ns.follow(expr.op0().type())!=
       ns.follow(expr.op1().type()))
      expr=false_exprt();
    else
    {
      equal_exprt equality_expr(expr.op0(), expr.op1());
      expr.swap(equality_expr);
    }
  }

  Forall_operands(it, expr)
    replace_array_equal(*it);
}

/// Rewrite index/member expressions in byte_extract to offset
static void adjust_byte_extract_rec(exprt &expr, const namespacet &ns)
{
  Forall_operands(it, expr)
    adjust_byte_extract_rec(*it, ns);

  if(
    expr.id() == ID_byte_extract_big_endian ||
    expr.id() == ID_byte_extract_little_endian)
  {
    byte_extract_exprt &be = to_byte_extract_expr(expr);
    if(
      be.op().id() == ID_symbol &&
      to_ssa_expr(be.op()).get_original_expr().get_bool(ID_C_invalid_object))
    {
      return;
    }

    object_descriptor_exprt ode;
    ode.build(expr, ns);

    be.op() = ode.root_object();
    be.offset() = ode.offset();
  }
}

void goto_symext::clean_expr(
  exprt &expr,
  statet &state,
  const bool write)
{
  replace_nondet(expr);
  dereference(expr, state, write);

  // make sure all remaining byte extract operations use the root
  // object to avoid nesting of with/update and byte_update when on
  // lhs
  if(write)
    adjust_byte_extract_rec(expr, ns);

  replace_array_equal(expr);
}
