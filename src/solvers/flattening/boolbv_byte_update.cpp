/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <cassert>

#include <arith_tools.h>
#include <byte_operators.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_byte_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_byte_update(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=3)
    throw "byte_update takes three operands";
    
  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();
  const exprt &op2=expr.op2();

  bool little_endian;
  
  if(expr.id()==ID_byte_update_little_endian)
    little_endian=true;
  else if(expr.id()==ID_byte_update_big_endian)
    little_endian=false;
  else
    assert(false);

  convert_bv(op0, bv);
  
  bvt op2_bv;
  convert_bv(op2, op2_bv);
  unsigned update_width=op2_bv.size();
  unsigned byte_width=8;
  
  if(update_width>bv.size()) update_width=bv.size();

  // see if the byte number is constant

  mp_integer index;
  if(!to_integer(op1, index))
  {
    // yes!
    mp_integer offset=index*8;
    
    if(offset+update_width>mp_integer(bv.size()) || offset<0)
    {
      // out of bounds
    }
    else
    {
      if(little_endian)
      {
        for(unsigned i=0; i<update_width; i++)
          bv[integer2long(offset+i)]=op2_bv[i];
      }
      else
      {
        endianness_mapt map_op0(op0.type(), little_endian, ns);
        endianness_mapt map_op2(op2.type(), little_endian, ns);
        
        unsigned offset_i=integer2long(offset);
        
        for(unsigned i=0; i<update_width; i++)
          bv[map_op0.map_bit(offset_i+i)]=op2_bv[map_op2.map_bit(i)];
      }
    }

    return;
  }

  // byte_update with variable index
  for(unsigned offset=0; offset<bv.size(); offset+=byte_width)
  {
    // index condition
    equal_exprt equality;
    equality.lhs()=op1;
    equality.rhs()=from_integer(offset/byte_width, op1.type());
    literalt equal=convert(equality);
    
    endianness_mapt map_op0(op0.type(), little_endian, ns);
    endianness_mapt map_op2(op2.type(), little_endian, ns);

    for(unsigned bit=0; bit<update_width; bit++)
      if(offset+bit<bv.size())
      {
        unsigned bv_o=map_op0.map_bit(offset+bit);
        unsigned op2_bv_o=map_op2.map_bit(bit);
        
        bv[bv_o]=prop.lselect(equal, op2_bv[op2_bv_o], bv[bv_o]);
      }
  }
}
