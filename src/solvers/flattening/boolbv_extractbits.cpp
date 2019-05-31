/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>

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

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    upper_as_int >= 0 && upper_as_int < src_bv.size(),
    "upper end of extracted bits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lower_as_int >= 0 && lower_as_int < src_bv.size(),
    "lower end of extracted bits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

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

  const std::size_t offset = numeric_cast_v<std::size_t>(lower_as_int);

  bvt result_bv(
    src_bv.begin() + narrow_cast<std::ptrdiff_t>(offset),
    src_bv.begin() + narrow_cast<std::ptrdiff_t>(offset + bv_width));

  return result_bv;
}
