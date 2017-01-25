/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <util/fixedbv.h>
#include <util/ieee_float.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/type_eq.h>

#include <cegis/control/value/control_types.h>

#define FLOAT_WIDTH 32u

double to_control_float(const constant_exprt &expr)
{
  const typet &data_type=expr.type();
  if (ID_fixedbv == data_type.id())
  {
    // TODO: Implement
    assert(false);
  }
  ieee_floatt ieee_float(expr);
  ieee_float.change_spec(ieee_float_spect::double_precision());
  return ieee_float.to_double();
}

exprt to_control_float_expr(const symbol_tablet &st, double value)
{
  const typet &data_type=control_float_value_type(st);
  if (ID_fixedbv == data_type.id())
  {
    const fixedbv_spect spec(to_fixedbv_type(data_type));
    const bool is_neg=value < 0.0;
    const mp_integer factor=pow(mp_integer(2), spec.width);
    double abs_value=is_neg ? -value : value;
    const mp_integer::llong_t converted=factor.to_long() * abs_value;
    fixedbvt bv;
    bv.spec=spec;
    bv.from_integer(converted);
    const constant_exprt constant_expr(bv.to_expr());
    if (!is_neg) return constant_expr;
    return unary_minus_exprt(constant_expr);
  }
  ieee_floatt ieee(ieee_float_spect::double_precision());
  ieee.from_double(value);
  const exprt result(ieee.to_expr());
  if (type_eq(result.type(), data_type, namespacet(st))) return result;
  return typecast_exprt(result, data_type);
}
