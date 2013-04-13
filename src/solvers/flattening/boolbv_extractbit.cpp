/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_extractbit(const extractbit_exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=2)
    throw "extractbit takes two operands";
    
  const bvt &bv0=convert_bv(operands[0]);

  // constant?
  if(operands[1].is_constant())
  {
    mp_integer o;
  
    if(to_integer(operands[1], o))
      throw "extractbit failed to convert constant index";

    if(o<0 || o>=bv0.size())
      return prop.new_variable(); // out of range!
    else
      return bv0[integer2long(o)];
  }

  if(operands[0].type().id()==ID_verilogbv)
  {
    // TODO
    assert(false);
  }
  else
  {
    unsigned width_op0=boolbv_width(operands[0].type());
    unsigned width_op1=boolbv_width(operands[1].type());

    if(width_op0==0 || width_op1==0)
      return SUB::convert_rest(expr);

    mp_integer index_width=
      std::max(address_bits(width_op0), mp_integer(width_op1));

    unsignedbv_typet index_type;
    index_type.set_width(integer2long(index_width));

    equal_exprt equality;
    equality.lhs()=operands[1]; // index operand

    if(index_type!=equality.lhs().type())
      equality.lhs().make_typecast(index_type);

    if(prop.has_set_to())
    {
      // free variable
      literalt l=prop.new_variable();

      // add implications
      for(unsigned i=0; i<bv0.size(); i++)
      {
        equality.rhs()=from_integer(i, index_type);
        literalt equal=prop.lequal(l, bv0[i]);
        prop.l_set_to_true(prop.limplies(convert(equality), equal));
      }

      return l;
    }
    else
    {
      literalt l=prop.new_variable();

      for(unsigned i=0; i<bv0.size(); i++)
      {
        equality.rhs()=from_integer(i, index_type);
        l=prop.lselect(convert(equality), bv0[i], l);
      }

      return l;
    }
  }
   
  return SUB::convert_rest(expr);
}
