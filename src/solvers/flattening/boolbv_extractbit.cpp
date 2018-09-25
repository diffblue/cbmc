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
  const bvt &src_bv = convert_bv(expr.src());

  if(expr.index().is_constant())
  {
    mp_integer index_as_int = numeric_cast_v<mp_integer>(expr.index());
    CHECK_RETURN(index_as_int >= 0 && index_as_int < src_bv.size());
    return src_bv[integer2size_t(index_as_int)];
  }

  INVARIANT(
    expr.src().type().id() != ID_verilog_signedbv &&
      expr.src().type().id() != ID_verilog_unsignedbv,
    "bitvector extract not implemented for verilog");

  std::size_t src_width = boolbv_width(expr.src().type());
  std::size_t index_width = boolbv_width(expr.index().type());

  if(src_width == 0 || index_width == 0)
    return SUB::convert_rest(expr);

  std::size_t index_type_width = std::max(address_bits(src_width), index_width);
  unsignedbv_typet index_type(index_type_width);

  equal_exprt equality;
  equality.lhs() = expr.index();

  if(index_type != equality.lhs().type())
    equality.lhs().make_typecast(index_type);

  if(prop.has_set_to())
  {
    // free variable
    literalt literal = prop.new_variable();

    // add implications
    for(std::size_t i = 0; i < src_bv.size(); i++)
    {
      equality.rhs() = from_integer(i, index_type);
      literalt equal = prop.lequal(literal, src_bv[i]);
      prop.l_set_to_true(prop.limplies(convert(equality), equal));
    }

    return literal;
    }
    else
    {
      literalt literal = prop.new_variable();

      for(std::size_t i = 0; i < src_bv.size(); i++)
      {
        equality.rhs()=from_integer(i, index_type);
        literal = prop.lselect(convert(equality), src_bv[i], literal);
      }

      return literal;
    }

  return SUB::convert_rest(expr);
}
