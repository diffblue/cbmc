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

  if(expr.operands().size()!=3)
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits takes three operands" << eom;
    throw 0;
  }

  mp_integer upper_as_int, lower_as_int;
  auto const &src_bv = convert_bv(expr.src());

  // We only do constants for now.
  // Should implement a shift here.
  if(
    to_integer(expr.op1(), upper_as_int) ||
    to_integer(expr.op2(), lower_as_int))
    return conversion_failed(expr);

  if(upper_as_int < 0 || upper_as_int >= src_bv.size())
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: second operand out of range: "
            << expr.pretty() << eom;
  }

  if(lower_as_int < 0 || lower_as_int >= src_bv.size())
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: third operand out of range: "
            << expr.pretty() << eom;
    throw 0;
  }

  if(lower_as_int > upper_as_int)
    std::swap(upper_as_int, lower_as_int);

  // now lower_as_int <= upper_as_int

  if((upper_as_int - lower_as_int + 1) != bv_width)
  {
    error().source_location=expr.find_source_location();
    error() << "extractbits: wrong width (expected "
            << (upper_as_int - lower_as_int + 1) << " but got " << bv_width
            << "): " << expr.pretty() << eom;
    throw 0;
  }

  const std::size_t offset = integer2unsigned(lower_as_int);

  bvt result_bv;
  result_bv.resize(bv_width);

  for(std::size_t i = 0; i < bv_width; i++)
    result_bv[i] = src_bv[offset + i];

  return result_bv;
}
