/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>

#include <std_expr.h>
#include <base_type.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_equality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_equality(const equality_exprt &expr)
{
  if(!base_type_eq(expr.op0().type(), expr.op1().type(), ns))
  {
    std::cout << "######### op0: " << expr.op0().pretty() << std::endl;
    std::cout << "######### op1: " << expr.op1().pretty() << std::endl;
    throw "equality without matching types";
  }

  // see if it is an unbounded array
  if(is_unbounded_array(expr.op0().type()))
    return record_array_equality(expr);

  bvt bv0, bv1;
  
  convert_bv(expr.op0(), bv0);
  convert_bv(expr.op1(), bv1);
    
  if(bv0.size()!=bv1.size())
  {
    std::cerr << "op0: " << expr.op0().pretty() << std::endl;
    std::cerr << "op0 size: " << bv0.size() << std::endl;
    std::cerr << "op1: " << expr.op1().pretty() << std::endl;
    std::cerr << "op1 size: " << bv1.size() << std::endl;
    throw "unexpected size mismatch on equality";
  }

  if(bv0.size()==0)
    throw "got zero-size BV";

  if(expr.op0().type().id()=="verilogbv")
  {
    // TODO
  }
  else
    return bv_utils.equal(bv0, bv1);
  
  return SUB::convert_rest(expr);
}
