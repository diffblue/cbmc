/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/throw_with_nested.h>

#include <solvers/lowering/expr_lowering.h>
#include <solvers/lowering/flatten_byte_extract_exceptions.h>

#include "bv_conversion_exceptions.h"
#include "bv_endianness_map.h"

bvt map_bv(const bv_endianness_mapt &map, const bvt &src)
{
  PRECONDITION(map.number_of_bits() == src.size());
  bvt result;
  result.reserve(src.size());

  for(std::size_t i=0; i<src.size(); i++)
  {
    const size_t mapped_index = map.map_bit(i);
    CHECK_RETURN(mapped_index < src.size());
    result.push_back(src[mapped_index]);
  }

  return result;
}

bvt boolbvt::convert_byte_extract(const byte_extract_exprt &expr)
{
  // if we extract from an unbounded array, call the flattening code
  if(is_unbounded_array(expr.op().type()))
  {
    try
    {
      return convert_bv(lower_byte_extract(expr, ns));
    }
    catch(const flatten_byte_extract_exceptiont &)
    {
      util_throw_with_nested(
        bitvector_conversion_exceptiont("Can't convert byte_extraction", expr));
    }
  }

  const std::size_t width = boolbv_width(expr.type());

  // special treatment for bit-fields and big-endian:
  // we need byte granularity
  #if 0
  if(expr.id()==ID_byte_extract_big_endian &&
     expr.type().id()==ID_c_bit_field &&
     (width%8)!=0)
  {
    byte_extract_exprt tmp=expr;
    // round up
    to_c_bit_field_type(tmp.type()).set_width(width+8-width%8);
    convert_byte_extract(tmp, bv);
    bv.resize(width); // chop down
    return;
  }
  #endif

  if(width==0)
    return conversion_failed(expr);

  // see if the byte number is constant and within bounds, else work from the
  // root object
  const auto op_bytes_opt = pointer_offset_size(expr.op().type(), ns);
  auto index = numeric_cast<mp_integer>(expr.offset());

  if(
    (!index.has_value() || !op_bytes_opt.has_value() ||
     *index < 0 || *index >= *op_bytes_opt) &&
    (expr.op().id() == ID_member ||
     expr.op().id() == ID_index ||
     expr.op().id() == ID_byte_extract_big_endian ||
     expr.op().id() == ID_byte_extract_little_endian))
  {
    object_descriptor_exprt o;
    o.build(expr.op(), ns);
    CHECK_RETURN(o.offset().id() != ID_unknown);
    if(o.offset().type() != expr.offset().type())
      o.offset().make_typecast(expr.offset().type());
    byte_extract_exprt be(
      expr.id(),
      o.root_object(),
      plus_exprt(o.offset(), expr.offset()),
      expr.type());

    return convert_bv(be);
  }

  const exprt &op=expr.op();
  PRECONDITION(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian);
  const bool little_endian = expr.id() == ID_byte_extract_little_endian;

  // first do op0
  const bv_endianness_mapt op_map(op.type(), little_endian, ns, boolbv_width);
  const bvt op_bv=map_bv(op_map, convert_bv(op));

  // do result
  bv_endianness_mapt result_map(expr.type(), little_endian, ns, boolbv_width);
  bvt bv;
  bv.resize(width);

  // see if the byte number is constant
  unsigned byte_width=8;

  if(index.has_value())
  {
    const mp_integer offset = *index * byte_width;

    for(std::size_t i=0; i<width; i++)
      // out of bounds?
      if(offset + i < 0 || offset + i >= op_bv.size())
        bv[i]=prop.new_variable();
      else
        bv[i] = op_bv[numeric_cast_v<std::size_t>(offset) + i];
  }
  else
  {
    std::size_t bytes=op_bv.size()/byte_width;

    if(prop.has_set_to())
    {
      // free variables
      for(std::size_t i=0; i<width; i++)
        bv[i]=prop.new_variable();

      // add implications

      // type of index operand
      const typet &constant_type = expr.offset().type();

      bvt equal_bv;
      equal_bv.resize(width);

      for(std::size_t i=0; i<bytes; i++)
      {
        std::size_t offset=i*byte_width;

        for(std::size_t j=0; j<width; j++)
          if(offset+j<op_bv.size())
            equal_bv[j]=prop.lequal(bv[j], op_bv[offset+j]);
          else
            equal_bv[j]=const_literal(true);

        prop.l_set_to_true(prop.limplies(
          convert(equal_exprt(expr.offset(), from_integer(i, constant_type))),
          prop.land(equal_bv)));
      }
    }
    else
    {
      // type of index operand
      const typet &constant_type = expr.offset().type();

      for(std::size_t i=0; i<bytes; i++)
      {
        literalt e =
          convert(equal_exprt(expr.offset(), from_integer(i, constant_type)));

        std::size_t offset=i*byte_width;

        for(std::size_t j=0; j<width; j++)
        {
          literalt l;

          if(offset+j<op_bv.size())
            l=op_bv[offset+j];
          else
            l=const_literal(false);

          if(i==0)
            bv[j]=l;
          else
            bv[j]=prop.lselect(e, l, bv[j]);
        }
      }
    }
  }

  // shuffle the result
  bv=map_bv(result_map, bv);

  return bv;
}
