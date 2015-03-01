/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "adjust_float_expressions.h"

/*******************************************************************\

Function: adjust_float_expressions

  Inputs:

 Outputs:

 Purpose: This adds the rounding mode to floating-point operations,
          including those in vectors and complex numbers.

\*******************************************************************/

void adjust_float_expressions(
  exprt &expr,
  const namespacet &ns)
{
  Forall_operands(it, expr)
    adjust_float_expressions(*it, ns);

  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_floatbv ||
     (type.id()==ID_complex &&
      ns.follow(type.subtype()).id()==ID_floatbv))
  {
    symbol_exprt rounding_mode=
      ns.lookup(CPROVER_PREFIX "rounding_mode").symbol_expr();
      
    rounding_mode.add_source_location()=expr.source_location();
  
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
    else if(expr.id()==ID_typecast)
    {
      const typecast_exprt &typecast_expr=to_typecast_expr(expr);
      
      const typet &src_type=typecast_expr.op().type();
      const typet &dest_type=typecast_expr.type();

      if(dest_type.id()==ID_floatbv &&
         src_type.id()==ID_floatbv)
      {
        // Casts from bigger to smaller float-type might round.
	// For smaller to bigger it is strictly redundant but
	// we leave this optimisation until later to simplify
	// the representation.
        expr.id(ID_floatbv_typecast);
        expr.operands().resize(2);
        expr.op1()=rounding_mode;
      }
      else if(dest_type.id()==ID_floatbv &&
              (src_type.id()==ID_signedbv ||
               src_type.id()==ID_unsignedbv ||
               src_type.id()==ID_c_enum_tag))
      {
        // casts from integer to float-type might round
        expr.id(ID_floatbv_typecast);
        expr.operands().resize(2);
        expr.op1()=rounding_mode;
      }
    }
  }
}

