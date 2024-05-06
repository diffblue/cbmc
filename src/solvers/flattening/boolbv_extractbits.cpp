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

  auto const &src_bv = convert_bv(expr.src());

  auto const maybe_index_as_int = numeric_cast<mp_integer>(expr.index());

  // We only do constants for now.
  // Should implement a shift here.
  if(!maybe_index_as_int.has_value())
    return conversion_failed(expr);

  auto index_as_int = maybe_index_as_int.value();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    index_as_int >= 0 && index_as_int < src_bv.size(),
    "index of extractbits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    index_as_int + bv_width - 1 < src_bv.size(),
    "index+width-1 of extractbits must be within the bitvector",
    expr.find_source_location(),
    irep_pretty_diagnosticst{expr});

  const std::size_t offset = numeric_cast_v<std::size_t>(index_as_int);

  bvt result_bv(src_bv.begin() + offset, src_bv.begin() + offset + bv_width);

  return result_bv;
}
