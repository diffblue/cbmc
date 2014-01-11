/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>

#include "goto_symex.h"

unsigned goto_symext::nondet_count=0;
unsigned goto_symext::dynamic_counter=0;
unsigned goto_symext::heap_counter=0;

/*******************************************************************\

Function: goto_symext::do_simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::do_simplify(exprt &expr)
{
  if(options.get_bool_option("simplify"))
    simplify(expr, ns);
}

/*******************************************************************\

Function: goto_symext::replace_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::replace_nondet(exprt &expr)
{
  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_nondet)
  {
    exprt new_expr(ID_nondet_symbol, expr.type());
    new_expr.set(ID_identifier, "symex::nondet"+i2string(nondet_count++));
    new_expr.location()=expr.location();
    expr.swap(new_expr);
  }
  else
    Forall_operands(it, expr)
      replace_nondet(*it);
}

/*******************************************************************\

Function: goto_symext::replace_heap_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::replace_heap_member(exprt &expr)
{
  if(expr.id()==ID_member && is_heap_type(expr.type()))
  {
    struct_typet struct_type = to_struct_type(ns.follow(expr.type().subtype()));
    member_exprt struct_expr = to_member_expr(expr);
    irep_idt heap_id = make_heap_id(struct_type.get_tag());
    heap_member_exprt hexpr(struct_expr.struct_op());
    hexpr.set_component_name(struct_expr.get_component_name());
    hexpr.location()=expr.location();
    hexpr.set_heap_id(heap_id);
    expr.swap(hexpr);
  }
  else
    Forall_operands(it, expr)
      replace_heap_member(*it);
}

