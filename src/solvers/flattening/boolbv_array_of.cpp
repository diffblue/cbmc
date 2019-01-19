/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/std_types.h>

/// Flatten arrays constructed from a single element.
bvt boolbvt::convert_array_of(const array_of_exprt &expr)
{
  DATA_INVARIANT(
    expr.type().id() == ID_array, "array_of expression shall have array type");

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

  const bvt &tmp = convert_bv(expr.what());

  INVARIANT(
    size * tmp.size() == width,
    "total array bit width shall equal the number of elements times the "
    "element bit with");

  bvt bv;
  bv.resize(width);

  auto b_it = tmp.begin();

  for(auto &b : bv)
  {
    b = *b_it;

    b_it++;

    if(b_it == tmp.end())
      b_it = tmp.begin();
  }

  return bv;
}
