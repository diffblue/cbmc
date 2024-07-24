/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/exception_utils.h>
#include <util/std_expr.h>

literalt boolbvt::convert_extractbit(const extractbit_exprt &expr)
{
  const bvt &src_bv = convert_bv(expr.src());
  const auto &index = expr.index();

  // constant?
  if(index.is_constant())
  {
    mp_integer index_as_integer =
      numeric_cast_v<mp_integer>(to_constant_expr(index));

    if(index_as_integer < 0 || index_as_integer >= src_bv.size())
      return prop.new_variable(); // out of range!
    else
      return src_bv[numeric_cast_v<std::size_t>(index_as_integer)];
  }

  if(
    expr.src().type().id() == ID_verilog_signedbv ||
    expr.src().type().id() == ID_verilog_unsignedbv)
  {
    throw unsupported_operation_exceptiont(
      "extractbit expression not implemented for verilog integers in "
      "flattening solver");
  }
  else
  {
    std::size_t src_bv_width = boolbv_width(expr.src().type());
    std::size_t index_bv_width = boolbv_width(index.type());

    if(src_bv_width == 0 || index_bv_width == 0)
      return SUB::convert_rest(expr);

    std::size_t index_width =
      std::max(address_bits(src_bv_width), index_bv_width);
    unsignedbv_typet index_type(index_width);

    const auto index_casted =
      typecast_exprt::conditional_cast(index, index_type);

    if(prop.has_set_to())
    {
      // free variable
      literalt literal = prop.new_variable();

      // add implications
      for(std::size_t i = 0; i < src_bv.size(); i++)
      {
        equal_exprt equality(index_casted, from_integer(i, index_type));
        if(prop.cnf_handled_well())
        {
          literalt index_eq = convert(equality);
          prop.lcnf({!index_eq, !literal, src_bv[i]});
          prop.lcnf({!index_eq, literal, !src_bv[i]});
        }
        else
        {
          literalt equal = prop.lequal(literal, src_bv[i]);
          prop.l_set_to_true(prop.limplies(convert(equality), equal));
        }
      }

      return literal;
    }
    else
    {
      literalt literal = prop.new_variable();

      for(std::size_t i = 0; i < src_bv.size(); i++)
      {
        equal_exprt equality(index_casted, from_integer(i, index_type));
        literal = prop.lselect(convert(equality), src_bv[i], literal);
      }

      return literal;
    }
  }
}
