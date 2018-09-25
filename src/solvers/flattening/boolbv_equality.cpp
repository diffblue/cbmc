/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_expr.h>
#include <util/base_type.h>
#include <util/invariant.h>

#include "bv_conversion_exceptions.h"
#include "flatten_byte_operators.h"

literalt boolbvt::convert_equality(const equal_exprt &expr)
{
  const bool is_base_type_eq =
    base_type_eq(expr.lhs().type(), expr.rhs().type(), ns);
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    is_base_type_eq,
    "types of expressions on each side of equality should match",
    irep_pretty_diagnosticst{expr.lhs()},
    irep_pretty_diagnosticst{expr.rhs()});

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

  const bvt &lhs_bv = convert_bv(expr.lhs());
  const bvt &rhs_bv = convert_bv(expr.rhs());

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs_bv.size() == rhs_bv.size(),
    "sizes of lhs and rhs bitvectors should match",
    irep_pretty_diagnosticst{expr.lhs()},
    "lhs size: " + std::to_string(lhs_bv.size()),
    irep_pretty_diagnosticst{expr.rhs()},
    "rhs size: " + std::to_string(rhs_bv.size()));

  if(lhs_bv.empty())
  {
    // An empty bit-vector comparison. It's not clear
    // what this is meant to say.
    return prop.new_variable();
  }

  return bv_utils.equal(lhs_bv, rhs_bv);
}

literalt boolbvt::convert_verilog_case_equality(
  const binary_relation_exprt &expr)
{
  // This is 4-valued comparison, i.e., z===z, x===x etc.
  // The result is always Boolean.

  const bool is_base_type_eq =
    base_type_eq(expr.lhs().type(), expr.rhs().type(), ns);
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    is_base_type_eq,
    "lhs and rhs types should match in verilog_case_equality",
    irep_pretty_diagnosticst{expr.lhs()},
    irep_pretty_diagnosticst{expr.rhs()});

  const bvt &lhs_bv = convert_bv(expr.lhs());
  const bvt &rhs_bv = convert_bv(expr.rhs());

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs_bv.size() == rhs_bv.size(),
    "bitvector arguments to verilog_case_equality should have the same size",
    irep_pretty_diagnosticst{expr.lhs()},
    "lhs size: " + std::to_string(lhs_bv.size()),
    irep_pretty_diagnosticst{expr.rhs()},
    "rhs size: " + std::to_string(rhs_bv.size()));

  if(expr.id()==ID_verilog_case_inequality)
    return !bv_utils.equal(lhs_bv, rhs_bv);
  else
    return bv_utils.equal(lhs_bv, rhs_bv);
}
