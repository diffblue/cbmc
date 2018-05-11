/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/simplify_expr.h>
#include <util/zero_initializer.h>

unsigned goto_symext::dynamic_counter=0;

void goto_symext::do_simplify(exprt &expr)
{
  if(symex_config.simplify_opt)
    simplify(expr, ns);
}

nondet_symbol_exprt symex_nondet_generatort::operator()(typet &type)
{
  irep_idt identifier = "symex::nondet" + std::to_string(nondet_count++);
  nondet_symbol_exprt new_expr(identifier, type);
  return new_expr;
}
<<<<<<< HEAD
=======

void goto_symext::replace_nondet(exprt &expr)
{
  if(expr.id()==ID_side_effect &&
     expr.get(ID_statement)==ID_nondet)
  {
    exprt nondet = nondet_initializer(
      expr.type(), expr.source_location(), ns, log.get_message_handler());

    // recursively replace nondet fields in structs or arrays
    if(nondet.id() != ID_side_effect)
    {
      replace_nondet(nondet);
      expr.swap(nondet);
      return;
    }

    nondet_symbol_exprt new_expr = build_symex_nondet(expr.type());
    new_expr.add_source_location()=expr.source_location();
    expr.swap(new_expr);
  }
  else
    Forall_operands(it, expr)
      replace_nondet(*it);
}
>>>>>>> 2846e8c... Explicitly initialise non-static objects with non-deterministic values
