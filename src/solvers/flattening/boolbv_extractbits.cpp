/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>

bvt boolbvt::convert_extractbits(const extractbits_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.operands().size()!=3)
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits takes three operands" << eom;
    throw 0;
  }

  mp_integer o1, o2;
  const bvt &bv0=convert_bv(expr.op0());

  // We only do constants for now.
  // Should implement a shift here.
  if(to_integer(expr.op1(), o1) ||
     to_integer(expr.op2(), o2))
    return conversion_failed(expr);

  if(o1<0 || o1>=bv0.size())
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: second operand out of range: "
            << expr.pretty() << eom;
  }

  if(o2<0 || o2>=bv0.size())
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: third operand out of range: "
            << expr.pretty() << eom;
    throw 0;
  }

  if(o2>o1)
    std::swap(o1, o2);

  // now o2<=o1

  if((o1-o2+1)!=width)
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: wrong width (expected " << (o1-o2+1)
            << " but got " << width << "): " << expr.pretty() << eom;
    throw 0;
  }

  std::size_t offset=integer2unsigned(o2);

  bvt bv;
  bv.resize(width);

  for(std::size_t i=0; i<width; i++)
    bv[i]=bv0[offset+i];

  return bv;
}
