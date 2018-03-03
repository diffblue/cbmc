/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_cbmc.h"

#include <util/arith_tools.h>
#include <util/replace_expr.h>

bvt bv_cbmct::convert_waitfor(const exprt &expr)
{
  if(expr.operands().size()!=4)
  {
    error().source_location=expr.find_source_location();
    error() << "waitfor expected to have four operands" << eom;
    throw 0;
  }

  exprt new_cycle;
  const exprt &old_cycle=expr.op0();
  const exprt &cycle_var=expr.op1();
  const exprt &bound=expr.op2();
  const exprt &predicate=expr.op3();

  make_free_bv_expr(expr.type(), new_cycle);

  mp_integer bound_value;
  if(to_integer(bound, bound_value))
  {
    error().source_location=expr.find_source_location();
    error() << "waitfor bound must be a constant" << eom;
    throw 0;
  }

  {
    // constraint: new_cycle>=old_cycle

    set_to_true(binary_relation_exprt(new_cycle, ID_ge, old_cycle));
  }

  {
    // constraint: new_cycle<=bound+1

    exprt one=from_integer(1, bound.type());
    const plus_exprt bound_plus1(bound, one);
    set_to_true(binary_relation_exprt(new_cycle, ID_le, bound_plus1));
  }

  for(mp_integer i=0; i<=bound_value; i=i+1)
  {
    // replace cycle_var by old_cycle+i;

    const plus_exprt old_cycle_plus_i(
      old_cycle, from_integer(i, old_cycle.type()));

    exprt tmp_predicate=predicate;
    replace_expr(cycle_var, old_cycle_plus_i, tmp_predicate);

    // CONSTRAINT:
    // if((cycle)<=bound) {
    //   if((cycle)<new_cycle)
    //     assume(!property);
    //   else if((cycle)==new_cycle)
    //     assume(property);

    {
      const binary_relation_exprt cycle_le_bound(
        old_cycle_plus_i, ID_le, bound);
      const binary_relation_exprt cycle_lt_new_cycle(
        old_cycle_plus_i, ID_lt, new_cycle);
      const and_exprt and_expr(cycle_le_bound, cycle_lt_new_cycle);

      implies_exprt top_impl(and_expr, tmp_predicate);
      top_impl.op1().make_not();

      set_to_true(top_impl);
    }

    {
      const binary_relation_exprt cycle_le_bound(
        old_cycle_plus_i, ID_le, bound);
      const equal_exprt cycle_eq_new_cycle(old_cycle_plus_i, new_cycle);
      const and_exprt and_expr(cycle_le_bound, cycle_eq_new_cycle);

      const implies_exprt top_impl(and_expr, tmp_predicate);

      set_to_true(top_impl);
    }
  }

  // result: new_cycle
  return convert_bitvector(new_cycle);
}

bvt bv_cbmct::convert_waitfor_symbol(const exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "waitfor_symbol expected to have one operand" << eom;
    throw 0;
  }

  exprt result;
  const exprt &bound=expr.op0();

  make_free_bv_expr(expr.type(), result);

  // constraint: result<=bound

  set_to_true(binary_relation_exprt(result, ID_le, bound));

  return convert_bitvector(result);
}

bvt bv_cbmct::convert_bitvector(const exprt &expr)
{
  if(expr.id()=="waitfor")
    return convert_waitfor(expr);

  if(expr.id()=="waitfor_symbol")
    return convert_waitfor_symbol(expr);

  return bv_pointerst::convert_bitvector(expr);
}
