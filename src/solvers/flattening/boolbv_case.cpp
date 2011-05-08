/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_case

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_case(const exprt &expr, bvt &bv)
{
  const std::vector<exprt> &operands=expr.operands();

  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);

  // make it free variables
  for(unsigned i=0; i<bv.size(); i++)
    bv[i]=prop.new_variable();

  if(operands.size()<3)
    throw "case takes at least three operands";

  if((operands.size()%2)!=1)
    throw "number of case operands must be odd";

  enum { FIRST, COMPARE, VALUE } what=FIRST;
  bvt compare_bv;
  literalt previous_compare=const_literal(false);
  literalt compare_literal=const_literal(false);

  forall_operands(it, expr)
  {
    bvt op;

    convert_bv(*it, op);

    switch(what)
    {
    case FIRST:
      compare_bv.swap(op);
      what=COMPARE;
      break;

    case COMPARE:
      if(compare_bv.size()!=op.size())
      {
        std::cerr << "compare operand: " << compare_bv.size()
                  << std::endl
                  << "operand: " << op.size() << std::endl
                  << it->pretty()
                  << std::endl;

        throw "size of compare operand does not match";
      }

      compare_literal=bv_utils.equal(compare_bv, op);
      compare_literal=prop.land(prop.lnot(previous_compare),
                           compare_literal);

      previous_compare=prop.lor(previous_compare, compare_literal);

      what=VALUE;
      break;

    case VALUE: 
      if(bv.size()!=op.size())
      {
        std::cerr << "result size: " << bv.size()
                  << std::endl
                  << "operand: " << op.size() << std::endl
                  << it->pretty()
                  << std::endl;

        throw "size of value operand does not match";
      }

      {
        literalt value_literal=bv_utils.equal(bv, op);

        prop.l_set_to_true(
          prop.limplies(compare_literal, value_literal));
      }

      what=COMPARE;
      break;

    default:
      assert(false);
    }
  }
}

