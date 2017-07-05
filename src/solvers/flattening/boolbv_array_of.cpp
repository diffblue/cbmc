/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <util/arith_tools.h>
#include <util/std_types.h>

#include "boolbv.h"

bvt boolbvt::convert_array_of(const array_of_exprt &expr)
{
  if(expr.type().id()!=ID_array)
    throw "array_of must be array-typed";

  const array_typet &array_type=to_array_type(expr.type());

  if(is_unbounded_array(array_type))
    return conversion_failed(expr);

  std::size_t width=boolbv_width(array_type);

  if(width==0)
  {
    // A zero-length array is acceptable;
    // an element with unknown size is not.
    if(boolbv_width(array_type.subtype())==0)
      return conversion_failed(expr);
    else
      return bvt();
  }

  const exprt &array_size=array_type.size();

  mp_integer size;

  if(to_integer(array_size, size))
    return conversion_failed(expr);

  const bvt &tmp=convert_bv(expr.op0());

  bvt bv;
  bv.resize(width);

  if(size*tmp.size()!=width)
    throw "convert_array_of: unexpected operand width";

  std::size_t offset=0;

  for(mp_integer i=0; i<size; i=i+1)
  {
    for(std::size_t j=0; j<tmp.size(); j++, offset++)
      bv[offset]=tmp[j];
  }

  assert(offset==bv.size());

  return bv;
}
