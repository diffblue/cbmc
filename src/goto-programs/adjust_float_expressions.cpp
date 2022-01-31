/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "adjust_float_expressions.h"

#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/floatbv_expr.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "goto_model.h"

irep_idt rounding_mode_identifier()
{
  return CPROVER_PREFIX "rounding_mode";
}

/// Iterate over an expression and check it or any of its subexpressions are
/// floating point operations that haven't been adjusted with a rounding mode
/// yet.
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
    (type.id() == ID_complex &&
     to_complex_type(type).subtype().id() == ID_floatbv))
  {
    if(
      expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
      expr.id() == ID_div)
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

void adjust_float_expressions(exprt &expr, const exprt &rounding_mode)
{
  if(!have_to_adjust_float_expressions(expr))
    return;

  // recursive call
  // Note that we do the recursion twice here; once in
  // `have_to_adjust_float_expressions` and once here. Presumably this is to
  // avoid breaking sharing (calling the non-const operands() function breaks
  // sharing)
  for(auto &op : expr.operands())
    adjust_float_expressions(op, rounding_mode);

  const typet &type = expr.type();

  if(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex &&
     to_complex_type(type).subtype().id() == ID_floatbv))
  {
    if(
      expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
      expr.id() == ID_div)
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
                                irep_idt());

      expr.operands().resize(3);
      to_ieee_float_op_expr(expr).rounding_mode() = rounding_mode;
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
      to_floatbv_typecast_expr(expr).rounding_mode() = rounding_mode;
    }
    else if(
      dest_type.id() == ID_floatbv &&
      (src_type.id() == ID_signedbv || src_type.id() == ID_unsignedbv ||
       src_type.id() == ID_c_enum_tag || src_type.id() == ID_c_bit_field))
    {
      // casts from integer to float-type might round
      expr.id(ID_floatbv_typecast);
      expr.operands().resize(2);
      to_floatbv_typecast_expr(expr).rounding_mode() = rounding_mode;
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
      to_floatbv_typecast_expr(expr).rounding_mode() =
        from_integer(ieee_floatt::ROUND_TO_ZERO, rounding_mode.type());
    }
  }
}

void adjust_float_expressions(exprt &expr, const namespacet &ns)
{
  if(!have_to_adjust_float_expressions(expr))
    return;

  symbol_exprt rounding_mode =
    ns.lookup(rounding_mode_identifier()).symbol_expr();

  rounding_mode.add_source_location() = expr.source_location();

  adjust_float_expressions(expr, rounding_mode);
}

void adjust_float_expressions(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  for(auto &i : goto_function.body.instructions)
    i.transform([&ns](exprt expr) -> optionalt<exprt> {
      if(have_to_adjust_float_expressions(expr))
      {
        adjust_float_expressions(expr, ns);
        return expr;
      }
      else
        return {};
    });
}

void adjust_float_expressions(
  goto_functionst &goto_functions,
  const namespacet &ns)
{
  for(auto &gf_entry : goto_functions.function_map)
    adjust_float_expressions(gf_entry.second, ns);
}

void adjust_float_expressions(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  adjust_float_expressions(goto_model.goto_functions, ns);
}
