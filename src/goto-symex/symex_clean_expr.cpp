/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_expr.h>
#include <expr_util.h>
#include <cprover_prefix.h>

#include "goto_symex.h"

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
      expr.make_false();
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

Function: goto_symext::adjust_float_expressions

  Inputs:

 Outputs:

 Purpose: This adds the rounding mode to floating-point operations,
          including those in vectors and complex numbers.

\*******************************************************************/

void goto_symext::adjust_float_expressions(exprt &expr)
{
  Forall_operands(it, expr)
    adjust_float_expressions(*it);

  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_floatbv ||
     (type.id()==ID_complex &&
      ns.follow(type.subtype()).id()==ID_floatbv))
  {
    symbol_exprt rounding_mode=
      symbol_expr(ns.lookup(CPROVER_PREFIX "rounding_mode"));
      
    rounding_mode.location()=expr.location();
  
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div)
    {
      // make sure we have binary expressions
      if(expr.operands().size()>2)
        expr=make_binary(expr);

      assert(expr.operands().size()==2);

      // now add rounding mode
      expr.id(expr.id()==ID_plus?ID_floatbv_plus:
              expr.id()==ID_minus?ID_floatbv_minus:
              expr.id()==ID_mult?ID_floatbv_mult:
                                 ID_floatbv_div);

      expr.operands().resize(3);
      expr.op2()=rounding_mode;
    }
  }
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
  dereference(expr, state, write);
  replace_array_equal(expr);
  adjust_float_expressions(expr);
}
