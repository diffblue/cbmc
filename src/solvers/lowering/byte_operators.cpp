/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "expr_lowering.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>

#include "flatten_byte_extract_exceptions.h"

static exprt bv_to_expr(
  const exprt &bitvector_expr,
  const typet &target_type,
  const namespacet &ns);

/// Convert a bitvector-typed expression \p bitvector_expr to a struct-typed
/// expression. See \ref bv_to_expr for an overview.
static struct_exprt bv_to_struct_expr(
  const exprt &bitvector_expr,
  const struct_typet &struct_type,
  const namespacet &ns)
{
  const struct_typet::componentst &components = struct_type.components();

  exprt::operandst operands;
  operands.reserve(components.size());
  std::size_t member_offset_bits = 0;
  for(const auto &comp : components)
  {
    const auto component_bits_opt = pointer_offset_bits(comp.type(), ns);
    std::size_t component_bits;
    if(component_bits_opt.has_value())
      component_bits = numeric_cast_v<std::size_t>(*component_bits_opt);
    else
      component_bits = to_bitvector_type(bitvector_expr.type()).get_width() -
                       member_offset_bits;

    if(component_bits == 0)
    {
      operands.push_back(constant_exprt{irep_idt{}, comp.type()});
      continue;
    }

    bitvector_typet type{bitvector_expr.type().id(), component_bits};
    operands.push_back(bv_to_expr(
      extractbits_exprt{bitvector_expr,
                        member_offset_bits + component_bits - 1,
                        member_offset_bits,
                        std::move(type)},
      comp.type(),
      ns));

    if(component_bits_opt.has_value())
      member_offset_bits += component_bits;
  }

  return struct_exprt{std::move(operands), struct_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to an array-typed
/// expression. See \ref bv_to_expr for an overview.
static array_exprt bv_to_array_expr(
  const exprt &bitvector_expr,
  const array_typet &array_type,
  const namespacet &ns)
{
  auto num_elements = numeric_cast<std::size_t>(array_type.size());
  auto subtype_bits = pointer_offset_bits(array_type.subtype(), ns);

  const std::size_t total_bits =
    to_bitvector_type(bitvector_expr.type()).get_width();
  if(!num_elements.has_value())
  {
    if(!subtype_bits.has_value() || *subtype_bits == 0)
      num_elements = total_bits;
    else
      num_elements = total_bits / numeric_cast_v<std::size_t>(*subtype_bits);
  }
  DATA_INVARIANT(
    !num_elements.has_value() || !subtype_bits.has_value() ||
      *subtype_bits * *num_elements == total_bits,
    "subtype width times array size should be total bitvector width");

  exprt::operandst operands;
  operands.reserve(*num_elements);
  for(std::size_t i = 0; i < *num_elements; ++i)
  {
    if(subtype_bits.has_value())
    {
      const std::size_t subtype_bits_int =
        numeric_cast_v<std::size_t>(*subtype_bits);
      bitvector_typet type{bitvector_expr.type().id(), subtype_bits_int};
      operands.push_back(bv_to_expr(
        extractbits_exprt{bitvector_expr,
                          ((i + 1) * subtype_bits_int) - 1,
                          i * subtype_bits_int,
                          std::move(type)},
        array_type.subtype(),
        ns));
    }
    else
    {
      operands.push_back(bv_to_expr(bitvector_expr, array_type.subtype(), ns));
    }
  }

  return array_exprt{std::move(operands), array_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to a vector-typed
/// expression. See \ref bv_to_expr for an overview.
static vector_exprt bv_to_vector_expr(
  const exprt &bitvector_expr,
  const vector_typet &vector_type,
  const namespacet &ns)
{
  const std::size_t num_elements =
    numeric_cast_v<std::size_t>(vector_type.size());
  auto subtype_bits = pointer_offset_bits(vector_type.subtype(), ns);
  DATA_INVARIANT(
    !subtype_bits.has_value() ||
      *subtype_bits * num_elements ==
        to_bitvector_type(bitvector_expr.type()).get_width(),
    "subtype width times vector size should be total bitvector width");

  exprt::operandst operands;
  operands.reserve(num_elements);
  for(std::size_t i = 0; i < num_elements; ++i)
  {
    if(subtype_bits.has_value())
    {
      const std::size_t subtype_bits_int =
        numeric_cast_v<std::size_t>(*subtype_bits);
      bitvector_typet type{bitvector_expr.type().id(), subtype_bits_int};
      operands.push_back(bv_to_expr(
        extractbits_exprt{bitvector_expr,
                          ((i + 1) * subtype_bits_int) - 1,
                          i * subtype_bits_int,
                          std::move(type)},
        vector_type.subtype(),
        ns));
    }
    else
    {
      operands.push_back(bv_to_expr(bitvector_expr, vector_type.subtype(), ns));
    }
  }

  return vector_exprt{std::move(operands), vector_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to a complex-typed
/// expression. See \ref bv_to_expr for an overview.
static complex_exprt bv_to_complex_expr(
  const exprt &bitvector_expr,
  const complex_typet &complex_type,
  const namespacet &ns)
{
  const std::size_t total_bits =
    to_bitvector_type(bitvector_expr.type()).get_width();
  const auto subtype_bits_opt = pointer_offset_bits(complex_type.subtype(), ns);
  std::size_t subtype_bits;
  if(subtype_bits_opt.has_value())
  {
    subtype_bits = numeric_cast_v<std::size_t>(*subtype_bits_opt);
    DATA_INVARIANT(
      subtype_bits * 2 == total_bits,
      "subtype width should be half of the total bitvector width");
  }
  else
    subtype_bits = total_bits / 2;

  const bitvector_typet type{bitvector_expr.type().id(), subtype_bits};

  return complex_exprt{
    bv_to_expr(
      extractbits_exprt{bitvector_expr, subtype_bits - 1, 0, type},
      complex_type.subtype(),
      ns),
    bv_to_expr(
      extractbits_exprt{
        bitvector_expr, subtype_bits * 2 - 1, subtype_bits, type},
      complex_type.subtype(),
      ns),
    complex_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to an expression of
/// type \p target_type. If \p target_type is a bitvector type this may be a
/// no-op or a typecast. For composite types such as structs, the bitvectors
/// corresponding to the individual members are extracted and then a compound
/// expression is built from those extracted members. When the size of a
/// component isn't constant we fall back to computing its size based on the
/// width of \p bitvector_expr.
/// \param bitvector_expr: Bitvector-typed expression to extract from.
/// \param target_type: Type of the expression to build.
/// \param ns: Namespace to resolve tag types.
/// \return Expression of type \p target_type constructed from sequences of bits
/// from \p bitvector_expr.
static exprt bv_to_expr(
  const exprt &bitvector_expr,
  const typet &target_type,
  const namespacet &ns)
{
  PRECONDITION(can_cast_type<bitvector_typet>(bitvector_expr.type()));

  if(
    can_cast_type<bitvector_typet>(target_type) ||
    target_type.id() == ID_c_enum || target_type.id() == ID_c_enum_tag ||
    target_type.id() == ID_string)
  {
    return simplify_expr(
      typecast_exprt::conditional_cast(bitvector_expr, target_type), ns);
  }

  if(target_type.id() == ID_struct)
  {
    return bv_to_struct_expr(bitvector_expr, to_struct_type(target_type), ns);
  }
  else if(target_type.id() == ID_struct_tag)
  {
    struct_exprt result = bv_to_struct_expr(
      bitvector_expr, ns.follow_tag(to_struct_tag_type(target_type)), ns);
    result.type() = target_type;
    return std::move(result);
  }
  else if(target_type.id() == ID_array)
  {
    return bv_to_array_expr(bitvector_expr, to_array_type(target_type), ns);
  }
  else if(target_type.id() == ID_vector)
  {
    return bv_to_vector_expr(bitvector_expr, to_vector_type(target_type), ns);
  }
  else if(target_type.id() == ID_complex)
  {
    return bv_to_complex_expr(bitvector_expr, to_complex_type(target_type), ns);
  }
  else
  {
    PRECONDITION_WITH_DIAGNOSTICS(
      false, "bv_to_expr does not yet support ", target_type.id_string());
  }
}

static exprt unpack_rec(
  const exprt &src,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const namespacet &ns,
  bool unpack_byte_array = false);

/// Rewrite an array or vector into its individual bytes.
/// \param src: array/vector to unpack
/// \param src_size: array/vector size; if not a constant and thus not set,
///   \p max_bytes must be a known constant value, otherwise we fail with an
///   exception
/// \param element_bits: bit width of array/vector elements
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled
///   with nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param ns: namespace for type lookups
/// \return array_exprt holding unpacked elements
static array_exprt unpack_array_vector(
  const exprt &src,
  const optionalt<mp_integer> &src_size,
  const mp_integer &element_bits,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const namespacet &ns)
{
  if(!src_size.has_value() && !max_bytes.has_value())
    throw non_const_array_sizet(src.type(), nil_exprt());

  exprt::operandst byte_operands;
  mp_integer first_element = 0;

  // refine the number of elements to extract in case the element width is known
  // and a multiple of bytes; otherwise we will expand the entire array/vector
  optionalt<mp_integer> num_elements = src_size;
  if(element_bits > 0 && element_bits % 8 == 0)
  {
    mp_integer el_bytes = element_bits / 8;

    if(!num_elements.has_value())
    {
      // turn bytes into elements, rounding up
      num_elements = (*max_bytes + el_bytes - 1) / el_bytes;
    }

    if(offset_bytes.has_value())
    {
      // compute offset as number of elements
      first_element = *offset_bytes / el_bytes;
      // insert offset_bytes-many nil bytes into the output array
      byte_operands.resize(
        numeric_cast_v<std::size_t>(*offset_bytes - (*offset_bytes % el_bytes)),
        from_integer(0, unsignedbv_typet(8)));
    }
  }

  // the maximum number of bytes is an upper bound in case the size of the
  // array/vector is unknown; if element_bits was usable above this will
  // have been turned into a number of elements already
  if(!num_elements)
    num_elements = *max_bytes;

  const exprt src_simp = simplify_expr(src, ns);

  for(mp_integer i = first_element; i < *num_elements; ++i)
  {
    exprt element;

    if(
      (src_simp.id() == ID_array || src_simp.id() == ID_vector) &&
      i < src_simp.operands().size())
    {
      const std::size_t index_int = numeric_cast_v<std::size_t>(i);
      element = src_simp.operands()[index_int];
    }
    else
    {
      element = index_exprt(src_simp, from_integer(i, index_type()));
    }

    // recursively unpack each element until so that we eventually just have an
    // array of bytes left
    exprt sub = unpack_rec(element, little_endian, {}, max_bytes, ns, true);
    byte_operands.insert(
      byte_operands.end(), sub.operands().begin(), sub.operands().end());
  }

  const std::size_t size = byte_operands.size();
  return array_exprt(
    std::move(byte_operands),
    array_typet(unsignedbv_typet(8), from_integer(size, size_type())));
}

/// Rewrite a complex_exprt into its individual bytes.
/// \param src: complex-typed expression to unpack
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param ns: namespace for type lookups
/// \return array_exprt holding unpacked elements
static array_exprt
unpack_complex(const exprt &src, bool little_endian, const namespacet &ns)
{
  const complex_typet &complex_type = to_complex_type(src.type());
  const typet &subtype = complex_type.subtype();

  auto subtype_bits = pointer_offset_bits(subtype, ns);
  CHECK_RETURN(subtype_bits.has_value());
  CHECK_RETURN(*subtype_bits % 8 == 0);

  exprt sub_real = unpack_rec(
    complex_real_exprt{src},
    little_endian,
    mp_integer{0},
    *subtype_bits / 8,
    ns,
    true);
  exprt::operandst byte_operands = std::move(sub_real.operands());

  exprt sub_imag = unpack_rec(
    complex_imag_exprt{src},
    little_endian,
    mp_integer{0},
    *subtype_bits / 8,
    ns,
    true);
  byte_operands.insert(
    byte_operands.end(),
    std::make_move_iterator(sub_imag.operands().begin()),
    std::make_move_iterator(sub_imag.operands().end()));

  const std::size_t size = byte_operands.size();
  return array_exprt{
    std::move(byte_operands),
    array_typet{unsignedbv_typet(8), from_integer(size, size_type())}};
}

/// Rewrite an object into its individual bytes.
/// \param src: object to unpack
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled with
///   nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param ns: namespace for type lookups
/// \param unpack_byte_array: if true, return unmodified \p src iff it is an
//    array of bytes
/// \return array of bytes in the sequence found in memory
/// \throws flatten_byte_extract_exceptiont Raised if unable to unpack the
/// object because of either non constant size, byte misalignment or
/// non-constant component width.
static exprt unpack_rec(
  const exprt &src,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const namespacet &ns,
  bool unpack_byte_array)
{
  if(src.type().id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src.type());
    const typet &subtype=array_type.subtype();

    auto element_bits = pointer_offset_bits(subtype, ns);
    CHECK_RETURN(element_bits.has_value());

    if(!unpack_byte_array && *element_bits == 8)
      return src;

    const auto constant_size_or_nullopt =
      numeric_cast<mp_integer>(array_type.size());
    return unpack_array_vector(
      src,
      constant_size_or_nullopt,
      *element_bits,
      little_endian,
      offset_bytes,
      max_bytes,
      ns);
  }
  else if(src.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(src.type());
    const typet &subtype = vector_type.subtype();

    auto element_bits = pointer_offset_bits(subtype, ns);
    CHECK_RETURN(element_bits.has_value());

    if(!unpack_byte_array && *element_bits == 8)
      return src;

    return unpack_array_vector(
      src,
      numeric_cast_v<mp_integer>(vector_type.size()),
      *element_bits,
      little_endian,
      offset_bytes,
      max_bytes,
      ns);
  }
  else if(src.type().id() == ID_complex)
  {
    return unpack_complex(src, little_endian, ns);
  }
  else if(src.type().id() == ID_struct || src.type().id() == ID_struct_tag)
  {
    const struct_typet &struct_type=to_struct_type(ns.follow(src.type()));
    const struct_typet::componentst &components=struct_type.components();

    mp_integer member_offset_bits = 0;

    exprt::operandst byte_operands;
    for(const auto &comp : components)
    {
      auto component_bits = pointer_offset_bits(comp.type(), ns);

      // the next member would be misaligned, abort
      if(!component_bits.has_value() || *component_bits % 8 != 0)
      {
        throw non_byte_alignedt(struct_type, comp, *component_bits);
      }

      optionalt<mp_integer> offset_in_member;
      optionalt<mp_integer> max_bytes_left;

      if(offset_bytes.has_value())
      {
        offset_in_member = *offset_bytes - member_offset_bits / 8;
        // if the offset is negative, offset_in_member remains unset, which has
        // the same effect as setting it to zero
        if(*offset_in_member < 0)
          offset_in_member.reset();
      }

      if(max_bytes.has_value())
      {
        max_bytes_left = *max_bytes - member_offset_bits / 8;
        if(*max_bytes_left < 0)
          break;
      }

      member_exprt member(src, comp.get_name(), comp.type());
      if(src.id() == ID_struct)
        simplify(member, ns);

      exprt sub = unpack_rec(
        member, little_endian, offset_in_member, max_bytes_left, ns, true);

      byte_operands.insert(
        byte_operands.end(), sub.operands().begin(), sub.operands().end());

      member_offset_bits += *component_bits;
    }

    const std::size_t size = byte_operands.size();
    return array_exprt(
      std::move(byte_operands),
      array_typet(unsignedbv_typet(8), from_integer(size, size_type())));
  }
  else if(src.type().id() == ID_union || src.type().id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(src.type()));
    const union_typet::componentst &components = union_type.components();

    mp_integer max_width = 0;
    typet max_comp_type;
    irep_idt max_comp_name;

    for(const auto &comp : components)
    {
      auto element_width = pointer_offset_bits(comp.type(), ns);

      if(!element_width.has_value() || *element_width <= max_width)
        continue;

      max_width = *element_width;
      max_comp_type = comp.type();
      max_comp_name = comp.get_name();
    }

    if(max_width > 0)
    {
      member_exprt member(src, max_comp_name, max_comp_type);
      return unpack_rec(
        member, little_endian, offset_bytes, max_bytes, ns, true);
    }
  }
  else if(src.type().id() == ID_pointer)
  {
    return unpack_rec(
      typecast_exprt(
        src, unsignedbv_typet(to_pointer_type(src.type()).get_width())),
      little_endian,
      offset_bytes,
      max_bytes,
      ns,
      unpack_byte_array);
  }
  else if(src.id() == ID_string_constant)
  {
    return unpack_rec(
      to_string_constant(src).to_array_expr(),
      little_endian,
      offset_bytes,
      max_bytes,
      ns,
      unpack_byte_array);
  }
  else if(src.id() == ID_constant && src.type().id() == ID_string)
  {
    return unpack_rec(
      string_constantt(to_constant_expr(src).get_value()).to_array_expr(),
      little_endian,
      offset_bytes,
      max_bytes,
      ns,
      unpack_byte_array);
  }
  else if(src.type().id()!=ID_empty)
  {
    // a basic type; we turn that into extractbits while considering
    // endianness
    auto bits_opt = pointer_offset_bits(src.type(), ns);
    mp_integer bits;

    if(bits_opt.has_value())
      bits = *bits_opt;
    else if(max_bytes.has_value())
      bits = *max_bytes * 8;
    else
      throw non_constant_widtht(src, nil_exprt());

    exprt::operandst byte_operands;
    for(mp_integer i=0; i<bits; i+=8)
    {
      extractbits_exprt extractbits(
        src,
        from_integer(i+7, index_type()),
        from_integer(i, index_type()),
        unsignedbv_typet(8));

      // endianness_mapt should be the point of reference for mapping out
      // endianness, but we need to work on elements here instead of
      // individual bits
      if(little_endian)
        byte_operands.push_back(extractbits);
      else
        byte_operands.insert(byte_operands.begin(), extractbits);
    }

    const std::size_t size = byte_operands.size();
    return array_exprt(
      std::move(byte_operands),
      array_typet(unsignedbv_typet(8), from_integer(size, size_type())));
  }

  return array_exprt(
    {}, array_typet(unsignedbv_typet(8), from_integer(0, size_type())));
}

/// Rewrite a byte extraction of a complex-typed result to byte extraction of
/// the individual components that make up a \ref complex_exprt.
/// \param src: Original byte extract expression
/// \param unpacked: Byte extraction with root operand expanded into array (via
///   \ref unpack_rec)
/// \param ns: Namespace
/// \return An expression if the subtype size is known, else `nullopt` so that a
/// fall-back to more generic code can be used.
static optionalt<exprt> lower_byte_extract_complex(
  const byte_extract_exprt &src,
  const byte_extract_exprt &unpacked,
  const namespacet &ns)
{
  const complex_typet &complex_type = to_complex_type(src.type());
  const typet &subtype = complex_type.subtype();

  auto subtype_bits = pointer_offset_bits(subtype, ns);
  if(!subtype_bits.has_value() || *subtype_bits % 8 != 0)
    return {};

  // offset remains unchanged
  byte_extract_exprt real{unpacked};
  real.type() = subtype;

  const plus_exprt new_offset{
    unpacked.offset(),
    from_integer(*subtype_bits / 8, unpacked.offset().type())};
  byte_extract_exprt imag{unpacked};
  imag.type() = subtype;
  imag.offset() = simplify_expr(new_offset, ns);

  return simplify_expr(
    complex_exprt{
      lower_byte_extract(real, ns), lower_byte_extract(imag, ns), complex_type},
    ns);
}

/// rewrite byte extraction from an array to byte extraction from a
/// concatenation of array index expressions
exprt lower_byte_extract(const byte_extract_exprt &src, const namespacet &ns)
{
  // General notes about endianness and the bit-vector conversion:
  // A single byte with value 0b10001000 is stored (in irept) as
  // exactly this string literal, and its bit-vector encoding will be
  // bvt bv={0,0,0,1,0,0,0,1}, i.e., bv[0]==0 and bv[7]==1
  //
  // A multi-byte value like x=256 would be:
  // - little-endian storage: ((char*)&x)[0]==0, ((char*)&x)[1]==1
  // - big-endian storage:    ((char*)&x)[0]==1, ((char*)&x)[1]==0
  // - irept representation: 0000000100000000
  // - bvt: {0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0}
  //         <... 8bits ...> <... 8bits ...>
  //
  // An array {0, 1} will be encoded as bvt bv={0,1}, i.e., bv[1]==1
  // concatenation(0, 1) will yield a bvt bv={1,0}, i.e., bv[1]==0
  //
  // The semantics of byte_extract(endianness, op, offset, T) is:
  // interpret ((char*)&op)+offset as the endianness-ordered storage
  // of an object of type T at address ((char*)&op)+offset
  // For some T x, byte_extract(endianness, x, 0, T) must yield x.
  //
  // byte_extract for a composite type T or an array will interpret
  // the individual subtypes with suitable endianness; the overall
  // order of components is not affected by endianness.
  //
  // Examples:
  // unsigned char A[4];
  // byte_extract_little_endian(A, 0, unsigned short) requests that
  // A[0],A[1] be interpreted as the storage of an unsigned short with
  // A[1] being the most-significant byte; byte_extract_big_endian for
  // the same operands will select A[0] as the most-significant byte.
  //
  // int A[2] = {0x01020304,0xDEADBEEF}
  // byte_extract_big_endian(A, 0, short) should yield 0x0102
  // byte_extract_little_endian(A, 0, short) should yield 0x0304
  // To obtain this we first compute byte arrays while taking into
  // account endianness:
  // big-endian byte representation: {01,02,03,04,DE,AB,BE,EF}
  // little-endian byte representation: {04,03,02,01,EF,BE,AB,DE}
  // We extract the relevant bytes starting from ((char*)A)+0:
  // big-endian: {01,02}; little-endian: {04,03}
  // Finally we place them in the appropriate byte order as indicated
  // by endianness:
  // big-endian: (short)concatenation(01,02)=0x0102
  // little-endian: (short)concatenation(03,04)=0x0304

  PRECONDITION(
    src.id() == ID_byte_extract_little_endian ||
    src.id() == ID_byte_extract_big_endian);
  const bool little_endian = src.id() == ID_byte_extract_little_endian;

  // determine an upper bound of the number of bytes we might need
  exprt upper_bound=size_of_expr(src.type(), ns);
  if(upper_bound.is_not_nil())
  {
    upper_bound = simplify_expr(
      plus_exprt(
        upper_bound,
        typecast_exprt::conditional_cast(src.offset(), upper_bound.type())),
      ns);
  }
  else if(src.type().id() == ID_empty)
    upper_bound = from_integer(0, size_type());

  const auto lower_bound_or_nullopt = numeric_cast<mp_integer>(src.offset());
  const auto upper_bound_or_nullopt = numeric_cast<mp_integer>(upper_bound);

  byte_extract_exprt unpacked(src);
  unpacked.op() = unpack_rec(
    src.op(),
    little_endian,
    lower_bound_or_nullopt,
    upper_bound_or_nullopt,
    ns);

  if(src.type().id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src.type());
    const typet &subtype=array_type.subtype();

    // consider ways of dealing with arrays of unknown subtype size or with a
    // subtype size that does not fit byte boundaries; currently we fall back to
    // stitching together consecutive elements down below
    auto element_bits = pointer_offset_bits(subtype, ns);
    if(element_bits.has_value() && *element_bits >= 1 && *element_bits % 8 == 0)
    {
      auto num_elements = numeric_cast<std::size_t>(array_type.size());
      if(!num_elements.has_value())
        num_elements = unpacked.op().operands().size();

      exprt::operandst operands;
      operands.reserve(*num_elements);
      for(std::size_t i = 0; i < *num_elements; ++i)
      {
        plus_exprt new_offset(
          unpacked.offset(),
          from_integer(i * (*element_bits) / 8, unpacked.offset().type()));

        byte_extract_exprt tmp(unpacked);
        tmp.type()=subtype;
        tmp.offset()=new_offset;

        operands.push_back(lower_byte_extract(tmp, ns));
      }

      return simplify_expr(array_exprt(std::move(operands), array_type), ns);
    }
  }
  else if(src.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(src.type());
    const typet &subtype = vector_type.subtype();

    // consider ways of dealing with vectors of unknown subtype size or with a
    // subtype size that does not fit byte boundaries; currently we fall back to
    // stitching together consecutive elements down below
    auto element_bits = pointer_offset_bits(subtype, ns);
    if(element_bits.has_value() && *element_bits >= 1 && *element_bits % 8 == 0)
    {
      const std::size_t num_elements =
        numeric_cast_v<std::size_t>(vector_type.size());

      exprt::operandst operands;
      operands.reserve(num_elements);
      for(std::size_t i = 0; i < num_elements; ++i)
      {
        plus_exprt new_offset(
          unpacked.offset(),
          from_integer(i * (*element_bits) / 8, unpacked.offset().type()));

        byte_extract_exprt tmp(unpacked);
        tmp.type() = subtype;
        tmp.offset() = simplify_expr(new_offset, ns);

        operands.push_back(lower_byte_extract(tmp, ns));
      }

      return simplify_expr(vector_exprt(std::move(operands), vector_type), ns);
    }
  }
  else if(src.type().id() == ID_complex)
  {
    auto result = lower_byte_extract_complex(src, unpacked, ns);
    if(result.has_value())
      return std::move(*result);

    // else fall back to generic lowering that uses bit masks, below
  }
  else if(src.type().id() == ID_struct || src.type().id() == ID_struct_tag)
  {
    const struct_typet &struct_type=to_struct_type(ns.follow(src.type()));
    const struct_typet::componentst &components=struct_type.components();

    bool failed=false;
    struct_exprt s({}, src.type());

    for(const auto &comp : components)
    {
      auto component_bits = pointer_offset_bits(comp.type(), ns);

      // the next member would be misaligned, abort
      if(
        !component_bits.has_value() || *component_bits == 0 ||
        *component_bits % 8 != 0)
      {
        failed=true;
        break;
      }

      plus_exprt new_offset(
        unpacked.offset(),
        typecast_exprt::conditional_cast(
          member_offset_expr(struct_type, comp.get_name(), ns),
          unpacked.offset().type()));

      byte_extract_exprt tmp(unpacked);
      tmp.type()=comp.type();
      tmp.offset()=new_offset;

      s.add_to_operands(lower_byte_extract(tmp, ns));
    }

    if(!failed)
      return simplify_expr(s, ns);
  }
  else if(src.type().id() == ID_union || src.type().id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(src.type()));
    const union_typet::componentst &components = union_type.components();

    mp_integer max_width = 0;
    typet max_comp_type;
    irep_idt max_comp_name;

    for(const auto &comp : components)
    {
      auto element_width = pointer_offset_bits(comp.type(), ns);

      if(!element_width.has_value() || *element_width <= max_width)
        continue;

      max_width = *element_width;
      max_comp_type = comp.type();
      max_comp_name = comp.get_name();
    }

    if(max_width > 0)
    {
      byte_extract_exprt tmp(unpacked);
      tmp.type() = max_comp_type;

      return union_exprt(
        max_comp_name, lower_byte_extract(tmp, ns), union_type);
    }
  }

  const exprt &root=unpacked.op();
  const exprt &offset=unpacked.offset();

  optionalt<typet> subtype;
  if(root.type().id() == ID_vector)
    subtype = to_vector_type(root.type()).subtype();
  else
    subtype = to_array_type(root.type()).subtype();

  auto subtype_bits = pointer_offset_bits(*subtype, ns);

  DATA_INVARIANT(
    subtype_bits.has_value() && *subtype_bits == 8,
    "offset bits are byte aligned");

  auto size_bits = pointer_offset_bits(unpacked.type(), ns);
  if(!size_bits.has_value())
  {
    auto op0_bits = pointer_offset_bits(unpacked.op().type(), ns);
    if(!op0_bits.has_value())
    {
      throw non_const_byte_extraction_sizet(unpacked);
    }
    else
      size_bits=op0_bits;
  }

  mp_integer num_elements =
    (*size_bits) / 8 + (((*size_bits) % 8 == 0) ? 0 : 1);

  // get 'width'-many bytes, and concatenate
  const std::size_t width_bytes = numeric_cast_v<std::size_t>(num_elements);
  exprt::operandst op;
  op.reserve(width_bytes);

  for(std::size_t i=0; i<width_bytes; i++)
  {
    // the most significant byte comes first in the concatenation!
    std::size_t offset_int=
      little_endian?(width_bytes-i-1):i;

    plus_exprt offset_i(from_integer(offset_int, offset.type()), offset);
    simplify(offset_i, ns);

    mp_integer index = 0;
    if(
      offset_i.is_constant() &&
      (root.id() == ID_array || root.id() == ID_vector) &&
      !to_integer(to_constant_expr(offset_i), index) &&
      index < root.operands().size() && index >= 0)
    {
      // offset is constant and in range
      op.push_back(root.operands()[numeric_cast_v<std::size_t>(index)]);
    }
    else
    {
      op.push_back(index_exprt(root, offset_i));
    }
  }

  if(width_bytes==1)
  {
    return simplify_expr(
      typecast_exprt::conditional_cast(op.front(), src.type()), ns);
  }
  else // width_bytes>=2
  {
    concatenation_exprt concatenation(
      std::move(op), bitvector_typet(subtype->id(), width_bytes * 8));

    return bv_to_expr(concatenation, src.type(), ns);
  }
}

static exprt lower_byte_update(
  const byte_update_exprt &src,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns);

/// Apply a byte update \p src to an array/vector of bytes using the byte
/// array \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array/vector expression reflecting all updates.
static exprt lower_byte_update_byte_array_vector(
  const byte_update_exprt &src,
  const typet &subtype,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  // apply 'array-update-with' num_elements times
  exprt result = src.op();

  for(std::size_t i = 0; i < value_as_byte_array.operands().size(); ++i)
  {
    const exprt &element = value_as_byte_array.operands()[i];

    const exprt where = simplify_expr(
      plus_exprt{src.offset(), from_integer(i, src.offset().type())}, ns);

    // skip elements that wouldn't change (skip over typecasts as we might have
    // some signed/unsigned char conversions)
    const exprt &e = skip_typecast(element);
    if(e.id() == ID_index)
    {
      const index_exprt &index_expr = to_index_expr(e);
      if(index_expr.array() == src.op() && index_expr.index() == where)
        continue;
    }

    exprt update_value;
    if(non_const_update_bound.has_value())
    {
      update_value = typecast_exprt::conditional_cast(
        if_exprt{binary_predicate_exprt{
                   from_integer(i, non_const_update_bound->type()),
                   ID_lt,
                   *non_const_update_bound},
                 element,
                 index_exprt{src.op(), where}},
        subtype);
    }
    else
      update_value = typecast_exprt::conditional_cast(element, subtype);

    if(result.id() != ID_with)
      result = with_exprt{result, where, update_value};
    else
      result.add_to_operands(where, update_value);
  }

  return simplify_expr(result, ns);
}

/// Apply a byte update \p src to an array/vector typed operand, using the byte
/// array \p value_as_byte_array as update value, when either the size of each
/// element or the overall array/vector size is not constant.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array/vector expression reflecting all updates.
static exprt lower_byte_update_array_vector_non_const(
  const byte_update_exprt &src,
  const typet &subtype,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                    ? ID_byte_extract_little_endian
                                    : ID_byte_extract_big_endian;

  // do all arithmetic below using index/offset types - the array theory
  // back-end is really picky about indices having the same type
  const exprt subtype_size = simplify_expr(
    typecast_exprt::conditional_cast(
      size_of_expr(subtype, ns), src.offset().type()),
    ns);

  // compute the index of the first element of the array/vector that may be
  // updated
  exprt first_index = div_exprt{src.offset(), subtype_size};
  simplify(first_index, ns);

  // compute the offset within that first element
  const exprt update_offset = mod_exprt{src.offset(), subtype_size};

  // compute the number of bytes (from the update value) that are going to be
  // consumed for updating the first element
  exprt initial_bytes = minus_exprt{subtype_size, update_offset};
  exprt update_bound;
  if(non_const_update_bound.has_value())
  {
    update_bound = typecast_exprt::conditional_cast(
      *non_const_update_bound, subtype_size.type());
  }
  else
  {
    update_bound =
      from_integer(value_as_byte_array.operands().size(), initial_bytes.type());
  }
  initial_bytes =
    if_exprt{binary_predicate_exprt{initial_bytes, ID_lt, update_bound},
             initial_bytes,
             update_bound};
  simplify(initial_bytes, ns);

  // encode the first update: update the original element at first_index with
  // initial_bytes-many bytes extracted from value_as_byte_array
  with_exprt result{
    src.op(),
    first_index,
    lower_byte_operators(
      byte_update_exprt{
        src.id(),
        index_exprt{src.op(), first_index},
        update_offset,
        byte_extract_exprt{extract_opcode,
                           value_as_byte_array,
                           from_integer(0, src.offset().type()),
                           array_typet{unsignedbv_typet{8}, initial_bytes}}},
      ns)};

  // We will update one array/vector element at a time - compute the number of
  // update values that will be consumed in each step. If we cannot determine a
  // constant value at this time we assume it's at least one byte. The
  // byte_extract_exprt within the loop uses the symbolic value (subtype_size),
  // we just need to make sure we make progress for the loop to terminate.
  std::size_t step_size = 1;
  if(subtype_size.is_constant())
    step_size = numeric_cast_v<std::size_t>(to_constant_expr(subtype_size));
  // Given the first update already encoded, keep track of the offset into the
  // update value. Again, the expressions within the loop use the symbolic
  // value, this is just an optimization in case we can determine a constant
  // offset.
  std::size_t offset = 0;
  if(initial_bytes.is_constant())
    offset = numeric_cast_v<std::size_t>(to_constant_expr(initial_bytes));

  std::size_t i = 1;
  for(; offset + step_size <= value_as_byte_array.operands().size();
      offset += step_size, ++i)
  {
    exprt where = simplify_expr(
      plus_exprt{first_index, from_integer(i, first_index.type())}, ns);

    exprt offset_expr = simplify_expr(
      plus_exprt{
        initial_bytes,
        mult_exprt{subtype_size, from_integer(i - 1, subtype_size.type())}},
      ns);

    exprt element = lower_byte_operators(
      byte_update_exprt{
        src.id(),
        index_exprt{src.op(), where},
        from_integer(0, src.offset().type()),
        byte_extract_exprt{extract_opcode,
                           value_as_byte_array,
                           std::move(offset_expr),
                           array_typet{unsignedbv_typet{8}, subtype_size}}},
      ns);

    result.add_to_operands(std::move(where), std::move(element));
  }

  // do the tail
  if(offset < value_as_byte_array.operands().size())
  {
    const std::size_t tail_size =
      value_as_byte_array.operands().size() - offset;

    exprt where = simplify_expr(
      plus_exprt{first_index, from_integer(i, first_index.type())}, ns);

    exprt element = lower_byte_operators(
      byte_update_exprt{
        src.id(),
        index_exprt{src.op(), where},
        from_integer(0, src.offset().type()),
        byte_extract_exprt{extract_opcode,
                           value_as_byte_array,
                           from_integer(offset, src.offset().type()),
                           array_typet{unsignedbv_typet{8},
                                       from_integer(tail_size, size_type())}}},
      ns);

    result.add_to_operands(std::move(where), std::move(element));
  }

  return simplify_expr(result, ns);
}

/// Apply a byte update \p src to an array/vector typed operand using the byte
/// array \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array/vector expression reflecting all updates.
static exprt lower_byte_update_array_vector(
  const byte_update_exprt &src,
  const typet &subtype,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  const bool is_array = src.type().id() == ID_array;
  exprt size;
  if(is_array)
    size = to_array_type(src.type()).size();
  else
    size = to_vector_type(src.type()).size();

  auto subtype_bits = pointer_offset_bits(subtype, ns);

  // fall back to bytewise updates in all non-constant or dubious cases
  if(
    !size.is_constant() || !src.offset().is_constant() ||
    !subtype_bits.has_value() || *subtype_bits == 0 || *subtype_bits % 8 != 0 ||
    non_const_update_bound.has_value())
  {
    return lower_byte_update_array_vector_non_const(
      src, subtype, value_as_byte_array, non_const_update_bound, ns);
  }

  std::size_t num_elements =
    numeric_cast_v<std::size_t>(to_constant_expr(size));
  mp_integer offset_bytes =
    numeric_cast_v<mp_integer>(to_constant_expr(src.offset()));

  exprt::operandst elements;
  elements.reserve(num_elements);

  std::size_t i = 0;
  // copy the prefix not affected by the update
  for(; i < num_elements && (i + 1) * *subtype_bits <= offset_bytes * 8; ++i)
    elements.push_back(index_exprt{src.op(), from_integer(i, index_type())});

  // the modified elements
  for(; i < num_elements &&
        i * *subtype_bits <
          (offset_bytes + value_as_byte_array.operands().size()) * 8;
      ++i)
  {
    mp_integer update_offset = offset_bytes - i * (*subtype_bits / 8);
    mp_integer update_elements = *subtype_bits / 8;
    exprt::operandst::const_iterator first =
      value_as_byte_array.operands().begin();
    exprt::operandst::const_iterator end = value_as_byte_array.operands().end();
    if(update_offset < 0)
    {
      INVARIANT(
        value_as_byte_array.operands().size() > -update_offset,
        "indices past the update should be handled above");
      first += numeric_cast_v<std::ptrdiff_t>(-update_offset);
    }
    else
    {
      update_elements -= update_offset;
      INVARIANT(
        update_elements > 0,
        "indices before the update should be handled above");
    }

    if(std::distance(first, end) > update_elements)
      end = first + numeric_cast_v<std::ptrdiff_t>(update_elements);
    exprt::operandst update_values{first, end};
    const std::size_t update_size = update_values.size();

    const byte_update_exprt bu{
      src.id(),
      index_exprt{src.op(), from_integer(i, index_type())},
      from_integer(update_offset < 0 ? 0 : update_offset, src.offset().type()),
      array_exprt{std::move(update_values),
                  array_typet{unsignedbv_typet{8},
                              from_integer(update_size, size_type())}}};
    elements.push_back(lower_byte_operators(bu, ns));
  }

  // copy the tail not affected by the update
  for(; i < num_elements; ++i)
    elements.push_back(index_exprt{src.op(), from_integer(i, index_type())});

  if(is_array)
    return simplify_expr(
      array_exprt{std::move(elements), to_array_type(src.type())}, ns);
  else
    return simplify_expr(
      vector_exprt{std::move(elements), to_vector_type(src.type())}, ns);
}

/// Apply a byte update \p src to a struct typed operand using the byte array
/// \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param struct_type: Type of the operand
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Struct expression reflecting all updates.
static exprt lower_byte_update_struct(
  const byte_update_exprt &src,
  const struct_typet &struct_type,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  exprt::operandst elements;
  elements.reserve(struct_type.components().size());

  mp_integer member_offset_bits = 0;
  for(const auto &comp : struct_type.components())
  {
    auto element_width = pointer_offset_bits(comp.type(), ns);

    // the next member would be misaligned, abort
    if(!element_width.has_value() || *element_width % 8 != 0)
    {
      throw non_byte_alignedt(struct_type, comp, *element_width);
    }

    member_exprt member{src.op(), comp.get_name(), comp.type()};

    // compute the update offset relative to this struct member - will be
    // negative if we are already in the middle of the update or beyond it
    exprt offset = simplify_expr(
      minus_exprt{src.offset(),
                  from_integer(member_offset_bits / 8, src.offset().type())},
      ns);
    auto offset_bytes = numeric_cast<mp_integer>(offset);
    // we don't need to update anything when
    // 1) the update offset is greater than the end of this member (thus the
    // relative offset is greater than this element) or
    // 2) the update offset plus the size of the update is less than the member
    // offset
    if(
      offset_bytes.has_value() &&
      (*offset_bytes * 8 >= *element_width ||
       (*offset_bytes < 0 &&
        -*offset_bytes >= value_as_byte_array.operands().size())))
    {
      elements.push_back(std::move(member));
      member_offset_bits += *element_width;
      continue;
    }
    else if(!offset_bytes.has_value())
    {
      const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                        ? ID_byte_extract_little_endian
                                        : ID_byte_extract_big_endian;

      const byte_extract_exprt byte_extract_expr{
        extract_opcode,
        src.op(),
        from_integer(0, src.offset().type()),
        array_typet{unsignedbv_typet{8}, size_of_expr(src.type(), ns)}};

      byte_update_exprt bu = src;
      bu.op() = lower_byte_extract(byte_extract_expr, ns);

      return lower_byte_extract(
        byte_extract_exprt{extract_opcode,
                           lower_byte_update_byte_array_vector(
                             bu,
                             unsignedbv_typet{8},
                             value_as_byte_array,
                             non_const_update_bound,
                             ns),
                           from_integer(0, src.offset().type()),
                           src.type()},
        ns);
    }

    mp_integer update_elements = *element_width / 8;
    exprt::operandst::const_iterator first =
      value_as_byte_array.operands().begin();
    exprt::operandst::const_iterator end = value_as_byte_array.operands().end();
    if(*offset_bytes < 0)
    {
      offset = from_integer(0, src.offset().type());
      INVARIANT(
        value_as_byte_array.operands().size() > -*offset_bytes,
        "members past the update should be handled above");
      first += numeric_cast_v<std::ptrdiff_t>(-*offset_bytes);
    }
    else
    {
      update_elements -= *offset_bytes;
      INVARIANT(
        update_elements > 0,
        "members before the update should be handled above");
    }

    if(std::distance(first, end) > update_elements)
      end = first + numeric_cast_v<std::ptrdiff_t>(update_elements);
    exprt::operandst update_values(first, end);
    const std::size_t update_size = update_values.size();

    byte_update_exprt bu{
      src.id(),
      std::move(member),
      offset,
      array_exprt{std::move(update_values),
                  array_typet{unsignedbv_typet{8},
                              from_integer(update_size, size_type())}}};
    elements.push_back(lower_byte_operators(bu, ns));

    member_offset_bits += *element_width;
  }

  return simplify_expr(struct_exprt{std::move(elements), struct_type}, ns);
}

/// Apply a byte update \p src to a union typed operand using the byte array
/// \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param union_type: Type of the operand
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Union expression reflecting all updates.
static exprt lower_byte_update_union(
  const byte_update_exprt &src,
  const union_typet &union_type,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  const union_typet::componentst &components = union_type.components();

  mp_integer max_width = 0;
  typet max_comp_type;
  irep_idt max_comp_name;

  for(const auto &comp : components)
  {
    auto element_width = pointer_offset_bits(comp.type(), ns);

    if(!element_width.has_value() || *element_width <= max_width)
      continue;

    max_width = *element_width;
    max_comp_type = comp.type();
    max_comp_name = comp.get_name();
  }

  PRECONDITION_WITH_DIAGNOSTICS(
    max_width > 0,
    "lower_byte_update of union of unknown size is not supported");

  byte_update_exprt bu = src;
  bu.op() = member_exprt{src.op(), max_comp_name, max_comp_type};
  bu.type() = max_comp_type;

  return union_exprt{
    max_comp_name,
    lower_byte_update(bu, value_as_byte_array, non_const_update_bound, ns),
    src.type()};
}

/// Apply a byte update \p src using the byte array \p value_as_byte_array as
/// update value.
/// \param src: Original byte-update expression
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Expression reflecting all updates.
static exprt lower_byte_update(
  const byte_update_exprt &src,
  const array_exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  if(src.type().id() == ID_array || src.type().id() == ID_vector)
  {
    optionalt<typet> subtype;
    if(src.type().id() == ID_vector)
      subtype = to_vector_type(src.type()).subtype();
    else
      subtype = to_array_type(src.type()).subtype();

    auto element_width = pointer_offset_bits(*subtype, ns);
    CHECK_RETURN(element_width.has_value());
    CHECK_RETURN(*element_width > 0);
    CHECK_RETURN(*element_width % 8 == 0);

    if(*element_width == 8)
      return lower_byte_update_byte_array_vector(
        src, *subtype, value_as_byte_array, non_const_update_bound, ns);
    else
      return lower_byte_update_array_vector(
        src, *subtype, value_as_byte_array, non_const_update_bound, ns);
  }
  else if(src.type().id() == ID_struct || src.type().id() == ID_struct_tag)
  {
    exprt result = lower_byte_update_struct(
      src,
      to_struct_type(ns.follow(src.type())),
      value_as_byte_array,
      non_const_update_bound,
      ns);
    result.type() = src.type();
    return result;
  }
  else if(src.type().id() == ID_union || src.type().id() == ID_union_tag)
  {
    exprt result = lower_byte_update_union(
      src,
      to_union_type(ns.follow(src.type())),
      value_as_byte_array,
      non_const_update_bound,
      ns);
    result.type() = src.type();
    return result;
  }
  else if(
    can_cast_type<bitvector_typet>(src.type()) ||
    src.type().id() == ID_c_enum || src.type().id() == ID_c_enum_tag)
  {
    // mask out the bits to be updated, shift the value according to the
    // offset and bit-or
    const auto type_width = pointer_offset_bits(src.type(), ns);
    CHECK_RETURN(type_width.has_value() && *type_width > 0);

    const std::size_t update_size = value_as_byte_array.operands().size();
    const std::size_t width =
      std::max(numeric_cast_v<std::size_t>(*type_width), update_size * 8);

    const bool is_little_endian = src.id() == ID_byte_update_little_endian;

    // build mask
    exprt mask;
    if(is_little_endian)
      mask =
        from_integer(power(2, update_size * 8) - 1, unsignedbv_typet{width});
    else
      mask = from_integer(
        power(2, width) - power(2, width - update_size * 8),
        unsignedbv_typet{width});

    const typet &offset_type = src.offset().type();
    mult_exprt offset_times_eight{src.offset(), from_integer(8, offset_type)};

    const binary_predicate_exprt offset_ge_zero{
      offset_times_eight, ID_ge, from_integer(0, offset_type)};

    if_exprt mask_shifted{offset_ge_zero,
                          shl_exprt{mask, offset_times_eight},
                          lshr_exprt{mask, offset_times_eight}};
    if(!is_little_endian)
      mask_shifted.true_case().swap(mask_shifted.false_case());

    // original_bits &= ~mask
    exprt val_before =
      typecast_exprt::conditional_cast(src.op(), unsignedbv_typet{width});
    bitand_exprt bitand_expr{val_before, bitnot_exprt{mask_shifted}};

    // concatenate and zero-extend the value
    concatenation_exprt value{exprt::operandst{value_as_byte_array.operands()},
                              unsignedbv_typet{update_size * 8}};
    if(is_little_endian)
      std::reverse(value.operands().begin(), value.operands().end());

    exprt zero_extended;
    if(width > update_size * 8)
    {
      zero_extended = concatenation_exprt{
        from_integer(0, unsignedbv_typet{width - update_size * 8}),
        value,
        unsignedbv_typet{width}};

      if(!is_little_endian)
        zero_extended.op0().swap(zero_extended.op1());
    }
    else
      zero_extended = value;

    // shift the value
    if_exprt value_shifted{offset_ge_zero,
                           shl_exprt{zero_extended, offset_times_eight},
                           lshr_exprt{zero_extended, offset_times_eight}};
    if(!is_little_endian)
      value_shifted.true_case().swap(value_shifted.false_case());

    // original_bits |= newvalue
    bitor_exprt bitor_expr{bitand_expr, value_shifted};

    return simplify_expr(
      typecast_exprt::conditional_cast(bitor_expr, src.type()), ns);
  }
  else
  {
    PRECONDITION_WITH_DIAGNOSTICS(
      false, "lower_byte_update does not yet support ", src.type().id_string());
  }
}

exprt lower_byte_update(const byte_update_exprt &src, const namespacet &ns)
{
  DATA_INVARIANT(
    src.id() == ID_byte_update_little_endian ||
      src.id() == ID_byte_update_big_endian,
    "byte update expression should either be little or big endian");

  // An update of a void-typed object or update by a void-typed value is the
  // source operand (this is questionable, but may arise when dereferencing
  // invalid pointers).
  if(src.type().id() == ID_empty || src.value().type().id() == ID_empty)
    return src.op();

  // byte_update lowering proceeds as follows:
  // 1) Determine the size of the update, with the size of the object to be
  // updated as an upper bound. We fail if neither can be determined.
  // 2) Turn the update value into a byte array of the size determined above.
  // 3) If the offset is not constant, turn the object into a byte array, and
  // use a "with" expression to encode the update; else update the values in
  // place.
  // 4) Construct a new object.
  std::size_t max_update_bytes = 0;
  optionalt<exprt> non_const_update_bound;
  exprt update_size_expr = size_of_expr(src.value().type(), ns);
  CHECK_RETURN(update_size_expr.is_not_nil());

  simplify(update_size_expr, ns);
  if(update_size_expr.is_constant())
    max_update_bytes =
      numeric_cast_v<std::size_t>(to_constant_expr(update_size_expr));
  else
  {
    exprt object_size_expr = size_of_expr(src.type(), ns);
    CHECK_RETURN(object_size_expr.is_not_nil());
    simplify(object_size_expr, ns);
    if(!object_size_expr.is_constant())
    {
      throw non_constant_widtht(src, update_size_expr);
    }

    max_update_bytes =
      numeric_cast_v<std::size_t>(to_constant_expr(object_size_expr));
    non_const_update_bound = std::move(update_size_expr);
  }

  const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                    ? ID_byte_extract_little_endian
                                    : ID_byte_extract_big_endian;

  const byte_extract_exprt byte_extract_expr{
    extract_opcode,
    src.value(),
    from_integer(0, src.offset().type()),
    array_typet{unsignedbv_typet{8},
                from_integer(max_update_bytes, size_type())}};

  const array_exprt value_as_byte_array =
    to_array_expr(lower_byte_extract(byte_extract_expr, ns));

  CHECK_RETURN(value_as_byte_array.operands().size() == max_update_bytes);

  return lower_byte_update(
    src, value_as_byte_array, non_const_update_bound, ns);
}

bool has_byte_operator(const exprt &src)
{
  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian ||
     src.id()==ID_byte_extract_little_endian ||
     src.id()==ID_byte_extract_big_endian)
    return true;

  forall_operands(it, src)
    if(has_byte_operator(*it))
      return true;

  return false;
}

exprt lower_byte_operators(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;

  // destroys any sharing, should use hash table
  Forall_operands(it, tmp)
  {
    *it = lower_byte_operators(*it, ns);
  }

  if(src.id()==ID_byte_update_little_endian ||
     src.id()==ID_byte_update_big_endian)
    return lower_byte_update(to_byte_update_expr(tmp), ns);
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
    return lower_byte_extract(to_byte_extract_expr(tmp), ns);
  else
    return tmp;
}
