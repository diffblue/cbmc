/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/simplify_expr.h>

unsigned goto_symext::nondet_count=0;
unsigned goto_symext::dynamic_counter=0;

void goto_symext::do_simplify(exprt &expr)
{
  if(simplify_opt)
    simplify(expr, ns);
}

nondet_symbol_exprt goto_symext::build_symex_nondet(typet &type)
{
  irep_idt identifier = "symex::nondet" + std::to_string(nondet_count++);
  nondet_symbol_exprt new_expr(identifier, type);
  return new_expr;
}

void goto_symext::replace_nondet(exprt &expr)
{
  if(expr.id()==ID_side_effect &&
     expr.get(ID_statement)==ID_nondet)
  {
    nondet_symbol_exprt new_expr = build_symex_nondet(expr.type());
    new_expr.add_source_location()=expr.source_location();
    expr.swap(new_expr);
  }
  else
    Forall_operands(it, expr)
      replace_nondet(*it);
}
