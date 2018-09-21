/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>
#include <algorithm>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

literalt boolbvt::convert_extractbit(const extractbit_exprt &expr)
{
  const bvt &bv0 = convert_bv(expr.src());

  // constant?
  if(expr.index().is_constant())
  {
    mp_integer o;

    if(to_integer(expr.index(), o))
      throw "extractbit failed to convert constant index";

    if(o<0 || o>=bv0.size())
      return prop.new_variable(); // out of range!
    else
      return bv0[integer2size_t(o)];
  }

  if(
    expr.src().type().id() == ID_verilog_signedbv ||
    expr.src().type().id() == ID_verilog_unsignedbv)
  {
    // TODO
    assert(false);
  }
  else
  {
    std::size_t width_op0 = boolbv_width(expr.src().type());
    std::size_t width_op1 = boolbv_width(expr.index().type());

    if(width_op0==0 || width_op1==0)
      return SUB::convert_rest(expr);

    std::size_t index_width = std::max(address_bits(width_op0), width_op1);
    unsignedbv_typet index_type(index_width);

    equal_exprt equality;
    equality.lhs() = expr.index();

    if(index_type!=equality.lhs().type())
      equality.lhs().make_typecast(index_type);

    if(prop.has_set_to())
    {
      // free variable
      literalt l=prop.new_variable();

      // add implications
      for(std::size_t i=0; i<bv0.size(); i++)
      {
        equality.rhs()=from_integer(i, index_type);
        literalt equal=prop.lequal(l, bv0[i]);
        prop.l_set_to_true(prop.limplies(convert(equality), equal));
      }

      return l;
    }
    else
    {
      literalt l=prop.new_variable();

      for(std::size_t i=0; i<bv0.size(); i++)
      {
        equality.rhs()=from_integer(i, index_type);
        l=prop.lselect(convert(equality), bv0[i], l);
      }

      return l;
    }
  }

  return SUB::convert_rest(expr);
}
