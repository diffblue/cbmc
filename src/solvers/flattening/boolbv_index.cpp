/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>

#include <arith_tools.h>
#include <std_expr.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_index(const index_exprt &expr, bvt &bv)
{
  if(expr.id()!=ID_index)
    throw "expected index expression";

  if(expr.operands().size()!=2)
    throw "index takes two operands";
    
  const exprt &array=expr.array();
  const exprt &index=expr.index();
  
  const array_typet &array_type=
    to_array_type(ns.follow(array.type()));

  // see if the array size is constant

  if(is_unbounded_array(array_type))
  {
    // use array decision procedure
  
    unsigned width=boolbv_width(expr.type());
    
    if(width==0)
      return conversion_failed(expr, bv);

    // free variables

    bv.resize(width);
    for(unsigned i=0; i<width; i++)
      bv[i]=prop.new_variable();

    record_array_index(expr);

    // record type if array is a symbol

    if(array.id()==ID_symbol)
      map.get_map_entry(
        to_symbol_expr(array).get_identifier(), array_type);

    // make sure we have the index in the cache
    bvt index_bv;
    convert_bv(index, index_bv);
    
    return;
  }

  // see if the index address is constant

  mp_integer index_value;
  if(!to_integer(index, index_value))
    return convert_index(array, index_value, bv);

  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  mp_integer array_size;
  if(to_integer(array_type.size(), array_size))
  {
    std::cout << to_array_type(array.type()).size().pretty() << std::endl;
    throw "failed to convert array size";
  }

  // get literals for the whole array

  bvt array_bv;

  convert_bv(array, array_bv);

  if(array_size*width!=array_bv.size())
    throw "unexpected array size";
    
  // TODO: maybe a shifter-like construction would be better

  if(prop.has_set_to())
  {
    // free variables

    bv.resize(width);
    for(unsigned i=0; i<width; i++)
      bv[i]=prop.new_variable();

    // add implications

    equal_exprt index_equality;
    index_equality.lhs()=index; // index operand

    bvt equal_bv;
    equal_bv.resize(width);

    for(mp_integer i=0; i<array_size; i=i+1)
    {
      index_equality.rhs()=from_integer(i, index_equality.lhs().type());

      if(index_equality.rhs().is_nil())
        throw "number conversion failed (1)";

      mp_integer offset=i*width;

      for(unsigned j=0; j<width; j++)
        equal_bv[j]=prop.lequal(bv[j],
                           array_bv[integer2long(offset+j)]);

      prop.l_set_to_true(
        prop.limplies(convert(index_equality), prop.land(equal_bv)));
    }
  }
  else
  {
    bv.resize(width);

    equal_exprt equality;
    equality.lhs()=index; // index operand

    typet constant_type=index.type(); // type of index operand
    
    assert(array_size>0);

    for(mp_integer i=0; i<array_size; i=i+1)
    {
      equality.op1()=from_integer(i, constant_type);
        
      literalt e=convert(equality);

      mp_integer offset=i*width;

      for(unsigned j=0; j<width; j++)
      {
        literalt l=array_bv[integer2long(offset+j)];

        if(i==0) // this initializes bv
          bv[j]=l;
        else
          bv[j]=prop.lselect(e, l, bv[j]);
      }
    }    
  }
}

/*******************************************************************\

Function: boolbvt::convert_index

  Inputs:

 Outputs:

 Purpose: index operator with constant index

\*******************************************************************/

void boolbvt::convert_index(
  const exprt &array,
  const mp_integer &index,
  bvt &bv)
{
  const array_typet &array_type=
    to_array_type(ns.follow(array.type()));

  unsigned width=boolbv_width(array_type.subtype());

  if(width==0)
    return conversion_failed(array, bv);

  bv.resize(width);
  
  bvt tmp;
  convert_bv(array, tmp); // recursive call

  mp_integer offset=index*width;

  if(offset>=0 &&
     offset+width<=mp_integer(tmp.size()))
  {
    // in bounds
    for(unsigned i=0; i<width; i++)
      bv[i]=tmp[integer2long(offset+i)];
  }
  else
  {
    // out of bounds
    for(unsigned i=0; i<width; i++)
      bv[i]=prop.new_variable();
  }
}
