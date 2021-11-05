/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>

bvt boolbvt::convert_extractbits(const extractbits_exprt &expr)
{
  const std::size_t bv_width = boolbv_width(expr.type());

  if(bv_width == 0)
    return conversion_failed(expr);

  auto const &src_bv = convert_bv(expr.src());

  auto const maybe_upper_as_int = numeric_cast<mp_integer>(expr.upper());
  auto const maybe_lower_as_int = numeric_cast<mp_integer>(expr.lower());

  // We only do constants for now.
  // Should implement a shift here.
  if(!maybe_upper_as_int.has_value() || !maybe_lower_as_int.has_value())
    return conversion_failed(expr);

  auto upper_as_int = maybe_upper_as_int.value();
  auto lower_as_int = maybe_lower_as_int.value();

  DATA_INVARIANT(
    lower_as_int <= upper_as_int,
    "upper bound must be greater or equal to lower bound");

  // now lower_as_int <= upper_as_int

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    (upper_as_int - lower_as_int + 1) == bv_width,
    "the difference between upper and lower end of the range must have the "
    "same width as the resulting bitvector type",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  bvt result_bv;

  // add out-of-bounds bits (if any) at the lower end
  if(lower_as_int < 0)
  {
    if(upper_as_int < 0)
    {
      lower_as_int -= upper_as_int + 1;
      upper_as_int = 0;
    }

    const std::size_t lower_out_of_bounds =
      numeric_cast_v<std::size_t>(-lower_as_int);
    result_bv = prop.new_variables(lower_out_of_bounds);
    lower_as_int = 0;
  }

  const std::size_t offset = numeric_cast_v<std::size_t>(lower_as_int);
  const std::size_t upper_size_t = numeric_cast_v<std::size_t>(upper_as_int);

  result_bv.reserve(bv_width);
  result_bv.insert(
    result_bv.end(),
    src_bv.begin() + std::min(offset, src_bv.size()),
    src_bv.begin() + std::min(src_bv.size(), upper_size_t + 1));

  // add out-of-bounds bits (if any) at the upper end
  if(upper_size_t >= src_bv.size())
  {
    bvt upper_oob_bits =
      prop.new_variables(upper_size_t - std::max(offset, src_bv.size()) + 1);
    result_bv.insert(
      result_bv.end(), upper_oob_bits.begin(), upper_oob_bits.end());
  }

  return result_bv;
}
