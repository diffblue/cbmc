/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/byte_operators.h>

#include <ansi-c/c_types.h>

#include "rewrite_union.h"

/*******************************************************************\

Function: rewrite_union

  Inputs:

 Outputs:

 Purpose: We rewrite u.c for unions u into
          byte_extract(u, 0)

\*******************************************************************/

void rewrite_union(
  exprt &expr,
  const namespacet &ns)
{
  Forall_operands(it, expr)
    rewrite_union(*it, ns);

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
