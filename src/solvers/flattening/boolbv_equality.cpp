/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

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

literalt boolbvt::convert_equality(const equal_exprt &expr)
{
  if(!base_type_eq(expr.lhs().type(), expr.rhs().type(), ns))
  {
    std::cout << "######### lhs: " << expr.lhs().pretty() << std::endl;
    std::cout << "######### rhs: " << expr.rhs().pretty() << std::endl;
    throw "equality without matching types";
  }

  // see if it is an unbounded array
  if(is_unbounded_array(expr.lhs().type()))
    return record_array_equality(expr);

  bvt bv0, bv1;
  
  convert_bv(expr.lhs(), bv0);
  convert_bv(expr.rhs(), bv1);
    
  if(bv0.size()!=bv1.size())
  {
    std::cerr << "lhs: " << expr.lhs().pretty() << std::endl;
    std::cerr << "lhs size: " << bv0.size() << std::endl;
    std::cerr << "rhs: " << expr.rhs().pretty() << std::endl;
    std::cerr << "rhs size: " << bv1.size() << std::endl;
    throw "unexpected size mismatch on equality";
  }

  if(bv0.size()==0)
    throw "got zero-size BV";

  if(expr.lhs().type().id()=="verilogbv")
  {
    // TODO
  }
  else
    return bv_utils.equal(bv0, bv1);
  
  return SUB::convert_rest(expr);
}
