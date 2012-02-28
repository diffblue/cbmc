/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <i2string.h>

#include <std_expr.h>
#include <base_type.h>

#include <langapi/language_util.h>

#include "flatten_byte_operators.h"
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
  {
    // flatten byte_update/byte_extract operators if needed

    if(has_byte_operator(expr))
    {
      exprt tmp=flatten_byte_operators(expr, ns);
      //std::cout << "X: " << from_expr(ns, "", tmp) << std::endl;
      return record_array_equality(to_equal_expr(tmp));
    }
    
    return record_array_equality(expr);
  }

  const bvt &bv0=convert_bv(expr.lhs());
  const bvt &bv1=convert_bv(expr.rhs());
    
  if(bv0.size()!=bv1.size())
  {
    std::cerr << "lhs: " << expr.lhs().pretty() << std::endl;
    std::cerr << "lhs size: " << bv0.size() << std::endl;
    std::cerr << "rhs: " << expr.rhs().pretty() << std::endl;
    std::cerr << "rhs size: " << bv1.size() << std::endl;
    throw "unexpected size mismatch on equality";
  }

  if(bv0.size()==0)
  {
    // An empty bit-vector comparison. It's not clear
    // what this is meant to say.
    return prop.new_variable();
  }

  if(expr.lhs().type().id()==ID_verilogbv)
  {
    // TODO
  }
  else
    return bv_utils.equal(bv0, bv1);
  
  return SUB::convert_rest(expr);
}
