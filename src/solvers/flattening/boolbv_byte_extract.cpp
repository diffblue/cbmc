/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>

#include "boolbv.h"
#include "flatten_byte_operators.h"

/*******************************************************************\

Function: boolbvt::convert_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_byte_extract(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=2)
    throw "byte_extract takes two operands";

  // if we extract from an unbounded array, call the flattening code
  if(is_unbounded_array(expr.op0().type()))
  {
    exprt tmp=flatten_byte_extract(expr, ns);
    bv=convert_bv(tmp);
    return;
  }

  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);    
    
  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();
  
  bool little_endian;
  
  if(expr.id()==ID_byte_extract_little_endian)
    little_endian=true;
  else if(expr.id()==ID_byte_extract_big_endian)
    little_endian=false;
  else
    assert(false);

  // first do op0
  
  const bvt &op0_bv=convert_bv(op0);
  
  // see if the byte number is constant

  mp_integer index;
  if(!to_integer(op1, index))
  {
    bv.resize(width);
    
    unsigned byte_width=8;
    mp_integer offset=index*byte_width;
    
    if(mp_integer(op0_bv.size())<offset+width || offset<0)
    {
      // out of bounds
      for(unsigned i=0; i<width; i++)
        bv[i]=prop.new_variable();
    }
    else
    {
      endianness_mapt op0_map(op0.type(), little_endian, ns);
      endianness_mapt bv_map(expr.type(), little_endian, ns);

      assert(width==byte_width*bv_map.size());
      
      unsigned offset_i=integer2long(offset);

      for(unsigned i=0; i<width; i++)
        bv[bv_map.map_bit(i)]=
          op0_bv[op0_map.map_bit(offset_i+i)];
    }
    
    return;
  }

  unsigned byte_width=8;
  unsigned bytes=op0_bv.size()/byte_width;
  
  if(prop.has_set_to())
  {
    // free variables

    bv.resize(width);
    for(unsigned i=0; i<width; i++)
      bv[i]=prop.new_variable();

    // add implications

    equal_exprt equality;
    equality.lhs()=op1; // index operand

    typet constant_type=op1.type(); // type of index operand

    bvt equal_bv;
    equal_bv.resize(width);

    for(unsigned i=0; i<bytes; i++)
    {
      equality.rhs()=from_integer(i, constant_type);

      unsigned offset=i*byte_width;

      for(unsigned j=0; j<width; j++)
        if(offset+j<op0_bv.size())
          equal_bv[j]=prop.lequal(bv[j], op0_bv[offset+j]);
        else
          equal_bv[j]=const_literal(true);

      prop.l_set_to_true(
        prop.limplies(convert(equality), prop.land(equal_bv)));
    }
  }
  else
  {
    bv.resize(width);

    equal_exprt equality;
    equality.lhs()=op1; // index operand

    typet constant_type(op1.type()); // type of index operand
    
    for(unsigned i=0; i<bytes; i++)
    {
      equality.rhs()=from_integer(i, constant_type);
        
      literalt e=convert(equality);

      unsigned offset=i*byte_width;

      for(unsigned j=0; j<width; j++)
      {
        literalt l;
        
        if(offset+j<op0_bv.size())
          l=op0_bv[offset+j];
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
