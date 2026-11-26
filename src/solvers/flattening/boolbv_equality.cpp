/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/invariant.h>
#include <util/std_expr.h>

#include "boolbv.h"

literalt boolbvt::convert_equality(const equal_exprt &expr)
{
  const bool equality_types_match = expr.lhs().type() == expr.rhs().type();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    equality_types_match,
    "types of expressions on each side of equality should match",
    irep_pretty_diagnosticst{expr.lhs()},
    irep_pretty_diagnosticst{expr.rhs()});

  // see if it is an unbounded array
  if(is_unbounded_array(expr.lhs().type()))
  {
    // flatten byte_update/byte_extract operators if needed
    const equal_exprt lowered =
      has_byte_operator(expr) ? to_equal_expr(lower_byte_operators(expr, ns))
                              : expr;

    // Equalities of (nested) arrays in constraints of the array decision
    // procedure compare all elements. Equalities of an array with itself,
    // which are used to ensure arrays are known to the decision procedure,
    // trivially hold. We cannot compare elements that do not have a fixed
    // width.
    if(
      converting_array_constraints || lowered.lhs() == lowered.rhs() ||
      !bv_width
         .get_width_opt(to_array_type(lowered.lhs().type()).element_type())
         .has_value())
    {
      return record_array_equality(lowered);
    }

    return convert_unbounded_array_equality(lowered);
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

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    expr.lhs().type() == expr.rhs().type(),
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

literalt boolbvt::convert_unbounded_array_equality(const equal_exprt &expr)
{
  const array_typet &array_type = to_array_type(expr.lhs().type());
  const exprt &size = array_type.size();
  // Arrays of infinite size, as used by the SMT2 front end, have the type of
  // their size as index type.
  const typet index_type =
    size.id() == ID_infinity ? size.type() : array_type.index_type();
  const std::string suffix = std::to_string(array_equality_counter++);

  // Elements at indices beyond the size of the array are irrelevant. Compare
  // rhs to lhs with all those elements replaced by the ones of rhs.
  exprt lhs = expr.lhs();
  if(size.is_not_nil() && size.id() != ID_infinity)
  {
    const symbol_exprt index{
      "boolbvt::array_equality_index$" + suffix, index_type};
    exprt in_bounds = binary_relation_exprt{
      index, ID_lt, typecast_exprt::conditional_cast(size, index_type)};
    if(index_type.id() == ID_signedbv)
    {
      in_bounds = and_exprt{
        binary_relation_exprt{index, ID_ge, from_integer(0, index_type)},
        std::move(in_bounds)};
    }
    lhs = array_comprehension_exprt{
      index,
      if_exprt{
        std::move(in_bounds),
        index_exprt{expr.lhs(), index},
        index_exprt{expr.rhs(), index}},
      array_type};
  }

  const literalt equal = record_array_equality(equal_exprt{lhs, expr.rhs()});

  // The array decision procedure only adds constraints of the form
  // equal ==> lhs[i] = rhs[i]. If the arrays are not equal, there must be an
  // index at which their elements differ.
  const symbol_exprt witness{
    "boolbvt::array_equality_witness$" + suffix, index_type};
  const literalt differ = convert(notequal_exprt{
    index_exprt{lhs, witness}, index_exprt{expr.rhs(), witness}});
  prop.lcnf(equal, differ);

  return equal;
}
