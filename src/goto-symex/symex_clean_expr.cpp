/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/cprover_prefix.h>
#include <util/byte_operators.h>

#include <ansi-c/c_types.h>

#include "adjust_float_expressions.h"
#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::replace_union_members

  Inputs:

 Outputs:

 Purpose: We rewrite u.c for unions u into
          byte_extract(u, 0)

\*******************************************************************/

void goto_symext::replace_union_members(exprt &expr)
{
  Forall_operands(it, expr)
    replace_union_members(*it);

  if(expr.id()==ID_member)
  {
    const exprt &op=to_member_expr(expr).struct_op();
    const typet &op_type=ns.follow(op.type());
    
    if(op_type.id()==ID_union)
    {
      exprt offset=gen_zero(index_type());
      byte_extract_exprt tmp(byte_extract_id(), op, offset, expr.type());
      expr=tmp;
    }
  }
}

/*******************************************************************\

Function: goto_symext::process_array_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::process_array_expr(exprt &expr)
{
  if(expr.id()==ID_if)
  {
    if_exprt &if_expr=to_if_expr(expr);
    process_array_expr(if_expr.true_case());
    process_array_expr(if_expr.false_case());
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
  else
    Forall_operands(it, expr)
      process_array_expr(*it);
}

/*******************************************************************\

Function: goto_symext::replace_array_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: goto_symext::clean_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::clean_expr(
  exprt &expr,
  statet &state,
  const bool write)
{
  replace_nondet(expr);
  replace_union_members(expr);
  dereference(expr, state, write);
  replace_array_equal(expr);
  adjust_float_expressions(expr, ns);
}
