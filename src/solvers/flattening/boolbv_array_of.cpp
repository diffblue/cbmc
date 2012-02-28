/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <std_types.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_array_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_array_of(const exprt &expr, bvt &bv)
{
  if(expr.operands().size()!=1)
    throw "array_of takes one operand";

  if(expr.type().id()!=ID_array)
    throw "array_of takes array-typed operand";
  
  const array_typet &array_type=to_array_type(expr.type());
  
  if(is_unbounded_array(array_type))
    return conversion_failed(expr, bv);

  unsigned width=boolbv_width(array_type);
  
  if(width==0)
    return conversion_failed(expr, bv);

  const exprt &array_size=array_type.size();

  mp_integer size;

  if(to_integer(array_size, size))
    return conversion_failed(expr, bv);
    
  const bvt &tmp=convert_bv(expr.op0());
    
  bv.resize(width);

  if(size*tmp.size()!=width)
    throw "convert_array_of: unexpected operand width";
    
  unsigned offset=0;

  for(mp_integer i=0; i<size; i=i+1)
  {
    for(unsigned j=0; j<tmp.size(); j++, offset++)
      bv[offset]=tmp[j];
  }
  
  assert(offset==bv.size());
}
