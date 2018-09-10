/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>

bvt boolbvt::convert_case(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_case);

  const std::vector<exprt> &operands=expr.operands();

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv;
  bv.resize(width);

  // make it free variables
  Forall_literals(it, bv)
    *it=prop.new_variable();

  DATA_INVARIANT(
    operands.size() >= 3, "case should have at least three operands");

  DATA_INVARIANT(
    operands.size() % 2 == 1, "number of case operands should be odd");

  enum { FIRST, COMPARE, VALUE } what=FIRST;
  bvt compare_bv;
  literalt previous_compare=const_literal(false);
  literalt compare_literal=const_literal(false);

  forall_operands(it, expr)
  {
    bvt op=convert_bv(*it);

    switch(what)
    {
    case FIRST:
      compare_bv.swap(op);
      what=COMPARE;
      break;

    case COMPARE:
      DATA_INVARIANT(
        compare_bv.size() == op.size(),
        std::string("size of compare operand does not match:\n") +
          "compare operand: " + std::to_string(compare_bv.size()) +
          "\noperand: " + std::to_string(op.size()) + '\n' + it->pretty());

      compare_literal=bv_utils.equal(compare_bv, op);
      compare_literal=prop.land(!previous_compare, compare_literal);

      previous_compare=prop.lor(previous_compare, compare_literal);

      what=VALUE;
      break;

    case VALUE:
      DATA_INVARIANT(
        bv.size() == op.size(),
        std::string("size of value operand does not match:\n") +
          "result size: " + std::to_string(bv.size()) +
          "\noperand: " + std::to_string(op.size()) + '\n' + it->pretty());

      {
        literalt value_literal=bv_utils.equal(bv, op);

        prop.l_set_to_true(
          prop.limplies(compare_literal, value_literal));
      }

      what=COMPARE;
      break;

    default:
      UNREACHABLE;
    }
  }

  return bv;
}
