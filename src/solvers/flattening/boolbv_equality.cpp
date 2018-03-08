/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_expr.h>
#include <util/base_type.h>
#include <util/invariant.h>

#include "flatten_byte_operators.h"

literalt boolbvt::convert_equality(const equal_exprt &expr)
{
  const bool is_base_type_eq =
    base_type_eq(expr.lhs().type(), expr.rhs().type(), ns);
  DATA_INVARIANT(
    is_base_type_eq,
    std::string("equality without matching types:\n") + "######### lhs: " +
      expr.lhs().pretty() + '\n' + "######### rhs: " + expr.rhs().pretty());

  // see if it is an unbounded array
  if(is_unbounded_array(expr.lhs().type()))
  {
    // flatten byte_update/byte_extract operators if needed

    if(has_byte_operator(expr))
    {
      exprt tmp=flatten_byte_operators(expr, ns);
      return record_array_equality(to_equal_expr(tmp));
    }

    return record_array_equality(expr);
  }

  const bvt &bv0=convert_bv(expr.lhs());
  const bvt &bv1=convert_bv(expr.rhs());

  DATA_INVARIANT(
    bv0.size() == bv1.size(),
    std::string("unexpected size mismatch on equality:\n") + "lhs: " +
      expr.lhs().pretty() + '\n' + "lhs size: " + std::to_string(bv0.size()) +
      '\n' + "rhs: " + expr.rhs().pretty() + '\n' +
      "rhs size: " + std::to_string(bv1.size()));

  if(bv0.empty())
  {
    // An empty bit-vector comparison. It's not clear
    // what this is meant to say.
    return prop.new_variable();
  }

  return bv_utils.equal(bv0, bv1);
}

literalt boolbvt::convert_verilog_case_equality(
  const binary_relation_exprt &expr)
{
  // This is 4-valued comparison, i.e., z===z, x===x etc.
  // The result is always Boolean.

  const bool is_base_type_eq =
    base_type_eq(expr.lhs().type(), expr.rhs().type(), ns);
  DATA_INVARIANT(
    is_base_type_eq,
    std::string("verilog_case_equality without matching types:\n") +
      "######### lhs: " + expr.lhs().pretty() + '\n' +
      "######### rhs: " + expr.rhs().pretty());

  const bvt &bv0=convert_bv(expr.lhs());
  const bvt &bv1=convert_bv(expr.rhs());

  DATA_INVARIANT(
    bv0.size() == bv1.size(),
    std::string("unexpected size mismatch on verilog_case_equality:\n") +
      "lhs: " + expr.lhs().pretty() + '\n' + "lhs size: " +
      std::to_string(bv0.size()) + '\n' + "rhs: " + expr.rhs().pretty() + '\n' +
      "rhs size: " + std::to_string(bv1.size()));

  if(expr.id()==ID_verilog_case_inequality)
    return !bv_utils.equal(bv0, bv1);
  else
    return bv_utils.equal(bv0, bv1);
}
