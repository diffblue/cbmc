/*******************************************************************\

Module: API to expression classes for bitvectors

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bitvector_expr.h"

#include "arith_tools.h"
#include "bitvector_types.h"
#include "mathematical_types.h"

shift_exprt::shift_exprt(
  exprt _src,
  const irep_idt &_id,
  const std::size_t _distance)
  : binary_exprt(std::move(_src), _id, from_integer(_distance, integer_typet()))
{
}

extractbit_exprt::extractbit_exprt(exprt _src, const std::size_t _index)
  : binary_predicate_exprt(
      std::move(_src),
      ID_extractbit,
      from_integer(_index, integer_typet()))
{
}

extractbits_exprt::extractbits_exprt(
  exprt _src,
  const std::size_t _index,
  typet _type)
  : expr_protectedt(ID_extractbits, std::move(_type))
{
  add_to_operands(std::move(_src), from_integer(_index, integer_typet()));
}

exprt update_bit_exprt::lower() const
{
  const auto width = to_bitvector_type(type()).get_width();
  auto src_bv_type = bv_typet(width);

  // build a mask 0...0 1
  auto mask_bv =
    make_bvrep(width, [](std::size_t index) { return index == 0; });
  auto mask_expr = constant_exprt(mask_bv, src_bv_type);

  // shift the mask by the index
  auto mask_shifted = shl_exprt(mask_expr, index());

  auto src_masked = bitand_exprt(
    typecast_exprt(src(), src_bv_type), bitnot_exprt(mask_shifted));

  // zero-extend the replacement bit to match src
  auto new_value_casted = zero_extend_exprt{new_value(), src_bv_type};

  // shift the replacement bits
  auto new_value_shifted = shl_exprt(new_value_casted, index());

  // or the masked src and the shifted replacement bits
  return typecast_exprt(
    bitor_exprt(src_masked, new_value_shifted), src().type());
}

exprt update_bits_exprt::lower() const
{
  const auto width = to_bitvector_type(type()).get_width();
  const auto new_value_width =
    to_bitvector_type(new_value().type()).get_width();
  auto src_bv_type = bv_typet(width);

  // build a mask 1...1 0...0
  auto mask_bv = make_bvrep(width, [new_value_width](std::size_t index) {
    return index >= new_value_width;
  });
  auto mask_expr = constant_exprt(mask_bv, src_bv_type);

  // shift the mask by the index
  auto mask_shifted = shl_exprt(mask_expr, index());

  auto src_masked =
    bitand_exprt(typecast_exprt(src(), src_bv_type), mask_shifted);

  // zero-extend or shrink the replacement bits to match src
  auto new_value_casted = zero_extend_exprt{new_value(), src_bv_type};

  // shift the replacement bits
  auto new_value_shifted = shl_exprt(new_value_casted, index());

  // or the masked src and the shifted replacement bits
  return typecast_exprt(
    bitor_exprt(src_masked, new_value_shifted), src().type());
}

exprt popcount_exprt::lower() const
{
  // Hacker's Delight, variant pop0:
  // x = (x & 0x55555555) + ((x >> 1) & 0x55555555);
  // x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
  // x = (x & 0x0F0F0F0F) + ((x >> 4) & 0x0F0F0F0F);
  // x = (x & 0x00FF00FF) + ((x >> 8) & 0x00FF00FF);
  // etc.
  // return x;
  // http://www.hackersdelight.org/permissions.htm

  // make sure the operand width is a power of two
  exprt x = op();
  const auto x_width = to_bitvector_type(x.type()).get_width();
  CHECK_RETURN(x_width >= 1);
  const std::size_t bits = address_bits(x_width);
  const std::size_t new_width = numeric_cast_v<std::size_t>(power(2, bits));

  const bool need_typecast =
    new_width > x_width || x.type().id() != ID_unsignedbv;

  if(need_typecast)
    x = typecast_exprt(x, unsignedbv_typet(new_width));

  // repeatedly compute x = (x & bitmask) + ((x >> shift) & bitmask)
  for(std::size_t shift = 1; shift < new_width; shift <<= 1)
  {
    // x >> shift
    lshr_exprt shifted_x(
      x, from_integer(shift, unsignedbv_typet(address_bits(shift) + 1)));
    // bitmask is a string of alternating shift-many bits starting from lsb set
    // to 1
    std::string bitstring;
    bitstring.reserve(new_width);
    for(std::size_t i = 0; i < new_width / (2 * shift); ++i)
      bitstring += std::string(shift, '0') + std::string(shift, '1');
    const mp_integer value = binary2integer(bitstring, false);
    const constant_exprt bitmask(integer2bvrep(value, new_width), x.type());
    // build the expression
    x = plus_exprt(bitand_exprt(x, bitmask), bitand_exprt(shifted_x, bitmask));
  }

  // the result is restricted to the result type
  return typecast_exprt::conditional_cast(x, type());
}

exprt count_leading_zeros_exprt::lower() const
{
  // x = x | (x >> 1);
  // x = x | (x >> 2);
  // x = x | (x >> 4);
  // x = x | (x >> 8);
  // etc.
  // return popcount(~x);

  // make sure the operand width is a power of two
  exprt x = op();
  const auto x_width = to_bitvector_type(x.type()).get_width();
  CHECK_RETURN(x_width >= 1);
  const std::size_t bits = address_bits(x_width);
  const std::size_t new_width = numeric_cast_v<std::size_t>(power(2, bits));

  const bool need_typecast =
    new_width > x_width || x.type().id() != ID_unsignedbv;

  if(need_typecast)
    x = typecast_exprt(x, unsignedbv_typet(new_width));

  // repeatedly compute x = x | (x >> shift)
  for(std::size_t shift = 1; shift < new_width; shift <<= 1)
  {
    // x >> shift
    lshr_exprt shifted_x(
      x, from_integer(shift, unsignedbv_typet(address_bits(shift) + 1)));
    // build the expression
    x = bitor_exprt{x, shifted_x};
  }

  // the result is restricted to the result type
  return popcount_exprt{
    bitnot_exprt{typecast_exprt::conditional_cast(x, op().type())}, type()}
    .lower();
}

exprt count_trailing_zeros_exprt::lower() const
{
  exprt x = op();

  // popcount(~(x | (~x + 1)))
  // compute -x using two's complement
  plus_exprt minus_x{bitnot_exprt{x}, from_integer(1, x.type())};
  bitor_exprt x_or_minus_x{x, std::move(minus_x)};
  popcount_exprt popcount{bitnot_exprt{std::move(x_or_minus_x)}};

  return typecast_exprt::conditional_cast(popcount.lower(), type());
}

exprt bitreverse_exprt::lower() const
{
  const std::size_t int_width = to_bitvector_type(type()).get_width();

  exprt::operandst result_bits;
  result_bits.reserve(int_width);

  const symbol_exprt to_reverse("to_reverse", op().type());
  for(std::size_t i = 0; i < int_width; ++i)
    result_bits.push_back(extractbit_exprt{to_reverse, i});

  return let_exprt{to_reverse, op(), concatenation_exprt{result_bits, type()}};
}

exprt plus_overflow_exprt::lower() const
{
  std::size_t lhs_ssize = to_bitvector_type(lhs().type()).get_width();
  if(lhs().type().id() == ID_unsignedbv)
    ++lhs_ssize;
  std::size_t rhs_ssize = to_bitvector_type(rhs().type()).get_width();
  if(rhs().type().id() == ID_unsignedbv)
    ++rhs_ssize;

  std::size_t ssize = std::max(lhs_ssize, rhs_ssize) + 1;
  signedbv_typet ssize_type{ssize};
  plus_exprt exact_result{
    typecast_exprt{lhs(), ssize_type}, typecast_exprt{rhs(), ssize_type}};

  return notequal_exprt{
    typecast_exprt{typecast_exprt{exact_result, lhs().type()}, ssize_type},
    exact_result};
}

exprt minus_overflow_exprt::lower() const
{
  std::size_t lhs_ssize = to_bitvector_type(lhs().type()).get_width();
  if(lhs().type().id() == ID_unsignedbv)
    ++lhs_ssize;
  std::size_t rhs_ssize = to_bitvector_type(rhs().type()).get_width();
  if(rhs().type().id() == ID_unsignedbv)
    ++rhs_ssize;

  std::size_t ssize = std::max(lhs_ssize, rhs_ssize) + 1;
  signedbv_typet ssize_type{ssize};
  minus_exprt exact_result{
    typecast_exprt{lhs(), ssize_type}, typecast_exprt{rhs(), ssize_type}};

  return notequal_exprt{
    typecast_exprt{typecast_exprt{exact_result, lhs().type()}, ssize_type},
    exact_result};
}

exprt mult_overflow_exprt::lower() const
{
  std::size_t lhs_ssize = to_bitvector_type(lhs().type()).get_width();
  if(lhs().type().id() == ID_unsignedbv)
    ++lhs_ssize;
  std::size_t rhs_ssize = to_bitvector_type(rhs().type()).get_width();
  if(rhs().type().id() == ID_unsignedbv)
    ++rhs_ssize;

  std::size_t ssize = lhs_ssize + rhs_ssize;
  signedbv_typet ssize_type{ssize};
  mult_exprt exact_result{
    typecast_exprt{lhs(), ssize_type}, typecast_exprt{rhs(), ssize_type}};

  return notequal_exprt{
    typecast_exprt{typecast_exprt{exact_result, lhs().type()}, ssize_type},
    exact_result};
}

exprt find_first_set_exprt::lower() const
{
  exprt x = op();
  const auto int_width = to_bitvector_type(x.type()).get_width();
  CHECK_RETURN(int_width >= 1);

  // bitwidth(x) - clz(x & ~((unsigned)x - 1));
  const unsignedbv_typet ut{int_width};
  minus_exprt minus_one{
    typecast_exprt::conditional_cast(x, ut), from_integer(1, ut)};
  count_leading_zeros_exprt clz{bitand_exprt{
    x, bitnot_exprt{typecast_exprt::conditional_cast(minus_one, x.type())}}};
  minus_exprt result{from_integer(int_width, x.type()), clz.lower()};

  return typecast_exprt::conditional_cast(result, type());
}

exprt zero_extend_exprt::lower() const
{
  const auto old_width = to_bitvector_type(op().type()).get_width();
  const auto new_width = to_bitvector_type(type()).get_width();

  if(new_width > old_width)
  {
    return concatenation_exprt{
      bv_typet{new_width - old_width}.all_zeros_expr(), op(), type()};
  }
  else // new_width <= old_width
  {
    return extractbits_exprt{op(), integer_typet{}.zero_expr(), type()};
  }
}
