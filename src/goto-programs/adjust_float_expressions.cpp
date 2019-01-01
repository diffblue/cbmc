/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "adjust_float_expressions.h"

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/ieee_float.h>
#include <util/arith_tools.h>

#include "goto_model.h"

static bool have_to_adjust_float_expressions(const exprt &expr)
{
  if(expr.id()==ID_floatbv_plus ||
     expr.id()==ID_floatbv_minus ||
     expr.id()==ID_floatbv_mult ||
     expr.id()==ID_floatbv_div ||
     expr.id()==ID_floatbv_div ||
     expr.id()==ID_floatbv_rem ||
     expr.id()==ID_floatbv_typecast)
    return false;

  const typet &type = expr.type();

  if(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex && type.subtype().id() == ID_floatbv))
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div ||
       expr.id()==ID_rem)
      return true;
  }

  if(expr.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(expr);

    const typet &src_type=typecast_expr.op().type();
    const typet &dest_type=typecast_expr.type();

    if(dest_type.id()==ID_floatbv &&
       src_type.id()==ID_floatbv)
      return true;
    else if(
      dest_type.id() == ID_floatbv &&
      (src_type.id() == ID_c_bit_field || src_type.id() == ID_signedbv ||
       src_type.id() == ID_unsignedbv || src_type.id() == ID_c_enum_tag))
      return true;
    else if(
      (dest_type.id() == ID_signedbv || dest_type.id() == ID_unsignedbv ||
       dest_type.id() == ID_c_enum_tag || dest_type.id() == ID_c_bit_field) &&
      src_type.id() == ID_floatbv)
      return true;
  }

  forall_operands(it, expr)
    if(have_to_adjust_float_expressions(*it))
      return true;

  return false;
}

/// This adds the rounding mode to floating-point operations, including those in
/// vectors and complex numbers.
void adjust_float_expressions(exprt &expr, const exprt &rounding_mode)
{
  if(!have_to_adjust_float_expressions(expr))
    return;

  // recursive call
  for(auto &op : expr.operands())
    adjust_float_expressions(op, rounding_mode);

  const typet &type = expr.type();

  if(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex && type.subtype().id() == ID_floatbv))
  {
    if(expr.id()==ID_plus || expr.id()==ID_minus ||
       expr.id()==ID_mult || expr.id()==ID_div ||
       expr.id()==ID_rem)
    {
      DATA_INVARIANT(
        expr.operands().size() >= 2,
        "arithmetic operations must have two or more operands");

      // make sure we have binary expressions
      if(expr.operands().size()>2)
      {
        expr=make_binary(expr);
        CHECK_RETURN(expr.operands().size() == 2);
      }

      // now add rounding mode
      expr.id(expr.id()==ID_plus?ID_floatbv_plus:
              expr.id()==ID_minus?ID_floatbv_minus:
              expr.id()==ID_mult?ID_floatbv_mult:
              expr.id()==ID_div?ID_floatbv_div:
              expr.id()==ID_rem?ID_floatbv_rem:
                                irep_idt());

      expr.operands().resize(3);
      expr.op2()=rounding_mode;
    }
  }

  if(expr.id()==ID_typecast)
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
    else if(
      dest_type.id() == ID_floatbv &&
      (src_type.id() == ID_signedbv || src_type.id() == ID_unsignedbv ||
       src_type.id() == ID_c_enum_tag || src_type.id() == ID_c_bit_field))
    {
      // casts from integer to float-type might round
      expr.id(ID_floatbv_typecast);
      expr.operands().resize(2);
      expr.op1()=rounding_mode;
    }
    else if(
      dest_type.id() == ID_floatbv &&
      (src_type.id() == ID_c_bool || src_type.id() == ID_bool))
    {
      // casts from bool or c_bool to float-type do not need rounding
    }
    else if(
      (dest_type.id() == ID_signedbv || dest_type.id() == ID_unsignedbv ||
       dest_type.id() == ID_c_enum_tag || dest_type.id() == ID_c_bit_field) &&
      src_type.id() == ID_floatbv)
    {
      // In C, casts from float to integer always round to zero,
      // irrespectively of the rounding mode that is currently set.
      // We will have to consider other programming languages
      // eventually.

      /* ISO 9899:1999
       *  6.3.1.4 Real floating and integer
       *  1 When a finite value of real floating type is converted
       *  to an integer type other than _Bool, the fractional part
       *  is discarded (i.e., the value is truncated toward zero).
       */
      expr.id(ID_floatbv_typecast);
      expr.operands().resize(2);
      expr.op1()=
        from_integer(ieee_floatt::ROUND_TO_ZERO, rounding_mode.type());
    }
  }
}

/// This adds the rounding mode to floating-point operations, including those in
/// vectors and complex numbers.
void adjust_float_expressions(exprt &expr, const namespacet &ns)
{
  if(!have_to_adjust_float_expressions(expr))
    return;

  symbol_exprt rounding_mode =
    ns.lookup(CPROVER_PREFIX "rounding_mode").symbol_expr();

  rounding_mode.add_source_location() = expr.source_location();

  adjust_float_expressions(expr, rounding_mode);
}

void adjust_float_expressions(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    adjust_float_expressions(it->code, ns);
    adjust_float_expressions(it->guard, ns);
  }
}

void adjust_float_expressions(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  Forall_goto_functions(it, goto_functions)
    adjust_float_expressions(it->second, ns);
}

void adjust_float_expressions(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  adjust_float_expressions(goto_model.goto_functions, ns);
}
