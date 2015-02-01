/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <util/endianness_map.h>

#include "boolbv.h"
#include "flatten_byte_operators.h"

/*******************************************************************\

Function: map_bv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt map_bv(const endianness_mapt &map, const bvt &src)
{
  assert(map.number_of_bits()==src.size());

  bvt result;
  result.resize(src.size(), const_literal(false));
  
  for(unsigned i=0; i<src.size(); i++)
  {
    size_t mapped_index=map.map_bit(i);
    assert(mapped_index<src.size());
    result[i]=src[mapped_index];
  }
  
  return result;
}

/*******************************************************************\

Function: boolbvt::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_byte_extract(
  const byte_extract_exprt &expr,
  bvt &bv)
{
  if(expr.operands().size()!=2)
    throw "byte_extract takes two operands";

  // if we extract from an unbounded array, call the flattening code
  if(is_unbounded_array(expr.op().type()))
  {
    exprt tmp=flatten_byte_extract(expr, ns);
    bv=convert_bv(tmp);
    return;
  }
  
  unsigned width=boolbv_width(expr.type());
  
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
    return conversion_failed(expr, bv);    
    
  const exprt &op=expr.op();
  const exprt &offset=expr.offset();
  
  bool little_endian;
  
  if(expr.id()==ID_byte_extract_little_endian)
    little_endian=true;
  else if(expr.id()==ID_byte_extract_big_endian)
    little_endian=false;
  else
    assert(false);

  // first do op0
  
  endianness_mapt op_map(op.type(), little_endian, ns);
  const bvt op_bv=map_bv(op_map, convert_bv(op));

  // do result
  endianness_mapt result_map(expr.type(), little_endian, ns);
  bv.resize(width);

  // see if the byte number is constant
  unsigned byte_width=8;

  mp_integer index;
  if(!to_integer(offset, index))
  {
    if(index<0)
      throw "byte_extract flatting with negative offset: "+expr.pretty();

    mp_integer offset=index*byte_width;
    
    unsigned offset_i=integer2unsigned(offset);

    for(unsigned i=0; i<width; i++)
      // out of bounds?
      if(offset<0 || offset_i+i>=op_bv.size())
        bv[i]=prop.new_variable();
      else
        bv[i]=op_bv[offset_i+i];
  }
  else
  {
    unsigned bytes=op_bv.size()/byte_width;
    
    if(prop.has_set_to())
    {
      // free variables
      for(unsigned i=0; i<width; i++)
        bv[i]=prop.new_variable();

      // add implications

      equal_exprt equality;
      equality.lhs()=offset; // index operand

      typet constant_type=offset.type(); // type of index operand

      bvt equal_bv;
      equal_bv.resize(width);

      for(unsigned i=0; i<bytes; i++)
      {
        equality.rhs()=from_integer(i, constant_type);

        unsigned offset=i*byte_width;

        for(unsigned j=0; j<width; j++)
          if(offset+j<op_bv.size())
            equal_bv[j]=prop.lequal(bv[j], op_bv[offset+j]);
          else
            equal_bv[j]=const_literal(true);

        prop.l_set_to_true(
          prop.limplies(convert(equality), prop.land(equal_bv)));
      }
    }
    else
    {
      equal_exprt equality;
      equality.lhs()=offset; // index operand

      typet constant_type(offset.type()); // type of index operand
      
      for(unsigned i=0; i<bytes; i++)
      {
        equality.rhs()=from_integer(i, constant_type);
          
        literalt e=convert(equality);

        unsigned offset=i*byte_width;

        for(unsigned j=0; j<width; j++)
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
}
