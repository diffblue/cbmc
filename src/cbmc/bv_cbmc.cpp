/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <replace_expr.h>

#include "bv_cbmc.h"

/*******************************************************************\

Function: bv_cbmct::convert_waitfor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_cbmct::convert_waitfor(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=4)
    throw "waitfor expected to have four operands";

  exprt new_cycle;
  const exprt &old_cycle=expr.op0();
  const exprt &cycle_var=expr.op1();
  const exprt &bound=expr.op2();
  const exprt &predicate=expr.op3();

  make_free_bv_expr(expr.type(), new_cycle);

  mp_integer bound_value;
  if(to_integer(bound, bound_value))
    throw "waitfor bound must be a constant";

  {
    // constraint: new_cycle>=old_cycle

    exprt rel_expr(ID_ge, bool_typet());
    rel_expr.copy_to_operands(new_cycle, old_cycle);
    set_to_true(rel_expr);
  }

  {
    // constraint: new_cycle<=bound+1

    exprt one=from_integer(1, bound.type());

    exprt bound_plus1(ID_plus, bound.type());
    bound_plus1.reserve_operands(2);
    bound_plus1.copy_to_operands(bound);
    bound_plus1.move_to_operands(one);

    exprt rel_expr(ID_le, bool_typet());
    rel_expr.copy_to_operands(new_cycle, bound_plus1);
    set_to_true(rel_expr);
  }

  for(mp_integer i=0; i<=bound_value; i=i+1)
  {
    // replace cycle_var by old_cycle+i;

    exprt old_cycle_plus_i(ID_plus, old_cycle.type());
    old_cycle_plus_i.operands().resize(2);
    old_cycle_plus_i.op0()=old_cycle;
    old_cycle_plus_i.op1()=from_integer(i, old_cycle.type());

    exprt tmp_predicate=predicate;
    replace_expr(cycle_var, old_cycle_plus_i, tmp_predicate);

    // CONSTRAINT:
    // if((cycle)<=bound) {
    //   if((cycle)<new_cycle)
    //     assume(!property);
    //   else if((cycle)==new_cycle)
    //     assume(property);

    {
      exprt cycle_le_bound(ID_le, bool_typet());
      cycle_le_bound.operands().resize(2);
      cycle_le_bound.op0()=old_cycle_plus_i;
      cycle_le_bound.op1()=bound;

      exprt cycle_lt_new_cycle(ID_lt, bool_typet());
      cycle_lt_new_cycle.operands().resize(2);
      cycle_lt_new_cycle.op0()=old_cycle_plus_i;
      cycle_lt_new_cycle.op1()=new_cycle;

      exprt and_expr(ID_and, bool_typet());
      and_expr.operands().resize(2);
      and_expr.op0().swap(cycle_le_bound);
      and_expr.op1().swap(cycle_lt_new_cycle);

      exprt top_impl(ID_implies, bool_typet());
      top_impl.reserve_operands(2);
      top_impl.move_to_operands(and_expr);
      top_impl.copy_to_operands(tmp_predicate);
      top_impl.op1().make_not();

      set_to_true(top_impl);
    }

    {
      exprt cycle_le_bound(ID_le, bool_typet());
      cycle_le_bound.operands().resize(2);
      cycle_le_bound.op0()=old_cycle_plus_i;
      cycle_le_bound.op1()=bound;

      exprt cycle_eq_new_cycle(ID_equal, bool_typet());
      cycle_eq_new_cycle.operands().resize(2);
      cycle_eq_new_cycle.op0()=old_cycle_plus_i;
      cycle_eq_new_cycle.op1()=new_cycle;

      exprt and_expr(ID_and, bool_typet());
      and_expr.operands().resize(2);
      and_expr.op0().swap(cycle_le_bound);
      and_expr.op1().swap(cycle_eq_new_cycle);

      exprt top_impl(ID_implies, bool_typet());
      top_impl.reserve_operands(2);
      top_impl.move_to_operands(and_expr);
      top_impl.copy_to_operands(tmp_predicate);

      set_to_true(top_impl);
    }
  }

  // result: new_cycle
  return convert_bitvector(new_cycle, bv);
}

/*******************************************************************\

Function: bv_cbmct::convert_waitfor_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_cbmct::convert_waitfor_symbol(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=1)
    throw "waitfor_symbol expected to have one operand";

  exprt result;
  const exprt &bound=expr.op0();

  make_free_bv_expr(expr.type(), result);

  // constraint: result<=bound

  exprt rel_expr(ID_le, bool_typet());
  rel_expr.copy_to_operands(result, bound);
  set_to_true(rel_expr);

  return convert_bitvector(result, bv);
}

/*******************************************************************\

Function: bv_cbmct::convert_bitvector

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_cbmct::convert_bitvector(const exprt &expr, bvt &bv)
{
  if(expr.id()=="waitfor")
    return convert_waitfor(expr, bv);

  if(expr.id()=="waitfor_symbol")
    return convert_waitfor_symbol(expr, bv);

  return bv_pointerst::convert_bitvector(expr, bv);
}
