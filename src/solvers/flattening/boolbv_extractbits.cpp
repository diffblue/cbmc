/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>

bvt boolbvt::convert_extractbits(const extractbits_exprt &expr)
{
  std::size_t target_bv_width = boolbv_width(expr.type());

  if(target_bv_width == 0)
    return conversion_failed(expr);

  const bvt &src_bv = convert_bv(expr.src());

  auto maybe_upper_as_int = numeric_cast<mp_integer>(expr.upper());
  auto maybe_lower_as_int = numeric_cast<mp_integer>(expr.lower());
  // We only do constants for now.
  // Should implement a shift here.
  if(!maybe_upper_as_int.has_value() || !maybe_lower_as_int.has_value())
    return conversion_failed(expr);
  mp_integer upper_as_int = maybe_upper_as_int.value();
  mp_integer lower_as_int = maybe_lower_as_int.value();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    upper_as_int >= 0 && upper_as_int < src_bv.size(),
    "the upper limit of a selectbits expression is in range",
    irep_pretty_diagnosticst{expr});

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lower_as_int >= 0 && lower_as_int < src_bv.size(),
    "the lower limit of a selectbits expression is in range",
    irep_pretty_diagnosticst{expr});

  if(lower_as_int > upper_as_int)
    std::swap(upper_as_int, lower_as_int);

  INVARIANT(
    lower_as_int <= upper_as_int,
    "the lower limit of selectbits is higher than the upper limit");

  auto const total_width = upper_as_int - lower_as_int + 1;
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    total_width == target_bv_width,
    "the number of extracted bits should match the width of the type the bits "
    "are being extracted to",
    irep_pretty_diagnosticst{expr});

  std::size_t offset = integer2unsigned(lower_as_int);

  bvt bv;
  bv.resize(target_bv_width);

  for(std::size_t i = 0; i < target_bv_width; i++)
    bv[i] = src_bv[offset + i];

  return bv;
}
