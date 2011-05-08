/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <i2string.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_extractbits(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);
  
  if(expr.type().id()!=ID_signedbv &&
     expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_bv)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=3)
    throw "extractbits takes three operands";

  mp_integer o1, o2;
  bvt bv0;

  convert_bv(expr.op0(), bv0);

  if(to_integer(expr.op1(), o1) ||
     to_integer(expr.op2(), o2))
    return conversion_failed(expr, bv);
    
  if(o1<0 || o1>=bv0.size())
    throw "extractbits: second operand out of range: "+expr.to_string();

  if(o2<0 || o2>=bv0.size())
    throw "extractbits: third operand out of range: "+expr.to_string();

  if(o2>o1) std::swap(o1, o2);

  // now o2<=o1

  if((o1-o2+1)!=width)
    throw "extractbits: wrong width (expected "+
          i2string(unsigned(integer2long(o1-o2+1)))+" but got "+
          i2string(width)+"): "+expr.to_string();

  unsigned offset=integer2long(o2);

  bv.resize(width);

  for(unsigned i=0; i<width; i++)
    bv[i]=bv0[offset+i];
}
