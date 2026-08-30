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

  if(maybe_index_as_int.has_value())
  {
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

  // For non-constant indices, encode
  //   extractbits(src, idx, T)
  // as the low bv_width bits of (src >> idx'), where idx' has been
  // zero-extended (or, if idx is wider than src, truncated) to
  // src_bv.size(). Truncation is sound because well-formed extractbits
  // indices satisfy idx + bv_width - 1 < src_bv.size() per the contract
  // for extractbits_exprt, so the upper bits of idx are guaranteed to be
  // zero. zero_extension (rather than sign-extension) is the correct
  // choice because indices are non-negative; this stays correct even when
  // idx has a signed type. Mirrors the encoding used by both SMT2
  // backends in convert_expr_to_smt.cpp / smt2_conv.cpp.
  bvt index_bv = convert_bv(expr.index());

  if(index_bv.size() < src_bv.size())
    index_bv = bv_utils.zero_extension(index_bv, src_bv.size());
  else if(index_bv.size() > src_bv.size())
    index_bv.resize(src_bv.size()); // truncate to low src_bv.size() bits

  const bvt shifted =
    bv_utils.shift(src_bv, bv_utilst::shiftt::SHIFT_LRIGHT, index_bv);

  return bvt{shifted.begin(), shifted.begin() + bv_width};
}
