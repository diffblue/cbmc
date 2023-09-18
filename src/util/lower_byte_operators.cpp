/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "byte_operators.h"
#include "c_types.h"
#include "endianness_map.h"
#include "expr_util.h"
#include "namespace.h"
#include "narrow.h"
#include "pointer_offset_size.h"
#include "simplify_expr.h"
#include "string_constant.h"

#include <algorithm>

static exprt bv_to_expr(
  const exprt &bitvector_expr,
  const typet &target_type,
  const endianness_mapt &endianness_map,
  const namespacet &ns);

struct boundst
{
  std::size_t lb;
  std::size_t ub;
};

/// Map bit boundaries according to endianness.
static boundst map_bounds(
  const endianness_mapt &endianness_map,
  std::size_t lower_bound,
  std::size_t upper_bound)
{
  boundst result;
  result.lb = lower_bound;
  result.ub = upper_bound;

  if(result.ub < endianness_map.number_of_bits())
  {
    result.lb = endianness_map.map_bit(result.lb);
    result.ub = endianness_map.map_bit(result.ub);

    // big-endian bounds need swapping
    if(result.ub < result.lb)
      std::swap(result.lb, result.ub);
  }

  return result;
}

/// changes the width of the given bitvector type
bitvector_typet adjust_width(const typet &src, std::size_t new_width)
{
  if(src.id() == ID_unsignedbv)
    return unsignedbv_typet(new_width);
  else if(src.id() == ID_signedbv)
    return signedbv_typet(new_width);
  else if(src.id() == ID_bv)
    return bv_typet(new_width);
  else if(src.id() == ID_c_enum) // we use the underlying type
    return adjust_width(to_c_enum_type(src).underlying_type(), new_width);
  else if(src.id() == ID_c_bit_field)
    return c_bit_field_typet(
      to_c_bit_field_type(src).underlying_type(), new_width);
  else
    PRECONDITION(false);
}

/// Convert a bitvector-typed expression \p bitvector_expr to a struct-typed
/// expression. See \ref bv_to_expr for an overview.
static struct_exprt bv_to_struct_expr(
  const exprt &bitvector_expr,
  const struct_typet &struct_type,
  const endianness_mapt &endianness_map,
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
      operands.push_back(
        bv_to_expr(bitvector_expr, comp.type(), endianness_map, ns));
      continue;
    }

    const auto bounds = map_bounds(
      endianness_map,
      member_offset_bits,
      member_offset_bits + component_bits - 1);
    bitvector_typet type = adjust_width(bitvector_expr.type(), component_bits);
    PRECONDITION(pointer_offset_bits(bitvector_expr.type(), ns).has_value());
    operands.push_back(bv_to_expr(
      extractbits_exprt{bitvector_expr, bounds.ub, bounds.lb, std::move(type)},
      comp.type(),
      endianness_map,
      ns));

    if(component_bits_opt.has_value())
      member_offset_bits += component_bits;
  }

  return struct_exprt{std::move(operands), struct_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to a union-typed
/// expression. See \ref bv_to_expr for an overview.
static exprt bv_to_union_expr(
  const exprt &bitvector_expr,
  const union_typet &union_type,
  const endianness_mapt &endianness_map,
  const namespacet &ns)
{
  const union_typet::componentst &components = union_type.components();

  if(components.empty())
    return empty_union_exprt{union_type};

  const auto widest_member = union_type.find_widest_union_component(ns);

  std::size_t component_bits;
  if(widest_member.has_value())
    component_bits = numeric_cast_v<std::size_t>(widest_member->second);
  else
    component_bits = to_bitvector_type(bitvector_expr.type()).get_width();

  if(component_bits == 0)
  {
    return union_exprt{
      components.front().get_name(),
      bv_to_expr(bitvector_expr, components.front().type(), endianness_map, ns),
      union_type};
  }

  const auto bounds = map_bounds(endianness_map, 0, component_bits - 1);
  bitvector_typet type = adjust_width(bitvector_expr.type(), component_bits);
  const irep_idt &component_name = widest_member.has_value()
                                     ? widest_member->first.get_name()
                                     : components.front().get_name();
  const typet &component_type = widest_member.has_value()
                                  ? widest_member->first.type()
                                  : components.front().type();
  PRECONDITION(pointer_offset_bits(bitvector_expr.type(), ns).has_value());
  return union_exprt{
    component_name,
    bv_to_expr(
      extractbits_exprt{bitvector_expr, bounds.ub, bounds.lb, std::move(type)},
      component_type,
      endianness_map,
      ns),
    union_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to an array-typed
/// expression. See \ref bv_to_expr for an overview.
static array_exprt bv_to_array_expr(
  const exprt &bitvector_expr,
  const array_typet &array_type,
  const endianness_mapt &endianness_map,
  const namespacet &ns)
{
  auto num_elements = numeric_cast<std::size_t>(array_type.size());
  auto subtype_bits = pointer_offset_bits(array_type.element_type(), ns);

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
      const auto bounds = map_bounds(
        endianness_map, i * subtype_bits_int, ((i + 1) * subtype_bits_int) - 1);
      bitvector_typet type =
        adjust_width(bitvector_expr.type(), subtype_bits_int);
      PRECONDITION(pointer_offset_bits(bitvector_expr.type(), ns).has_value());
      operands.push_back(bv_to_expr(
        extractbits_exprt{
          bitvector_expr, bounds.ub, bounds.lb, std::move(type)},
        array_type.element_type(),
        endianness_map,
        ns));
    }
    else
    {
      operands.push_back(bv_to_expr(
        bitvector_expr, array_type.element_type(), endianness_map, ns));
    }
  }

  return array_exprt{std::move(operands), array_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to a vector-typed
/// expression. See \ref bv_to_expr for an overview.
static vector_exprt bv_to_vector_expr(
  const exprt &bitvector_expr,
  const vector_typet &vector_type,
  const endianness_mapt &endianness_map,
  const namespacet &ns)
{
  const std::size_t num_elements =
    numeric_cast_v<std::size_t>(vector_type.size());
  auto subtype_bits = pointer_offset_bits(vector_type.element_type(), ns);
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
      const auto bounds = map_bounds(
        endianness_map, i * subtype_bits_int, ((i + 1) * subtype_bits_int) - 1);
      bitvector_typet type =
        adjust_width(bitvector_expr.type(), subtype_bits_int);
      PRECONDITION(pointer_offset_bits(bitvector_expr.type(), ns).has_value());
      operands.push_back(bv_to_expr(
        extractbits_exprt{
          bitvector_expr, bounds.ub, bounds.lb, std::move(type)},
        vector_type.element_type(),
        endianness_map,
        ns));
    }
    else
    {
      operands.push_back(bv_to_expr(
        bitvector_expr, vector_type.element_type(), endianness_map, ns));
    }
  }

  return vector_exprt{std::move(operands), vector_type};
}

/// Convert a bitvector-typed expression \p bitvector_expr to a complex-typed
/// expression. See \ref bv_to_expr for an overview.
static complex_exprt bv_to_complex_expr(
  const exprt &bitvector_expr,
  const complex_typet &complex_type,
  const endianness_mapt &endianness_map,
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

  const auto bounds_real = map_bounds(endianness_map, 0, subtype_bits - 1);
  const auto bounds_imag =
    map_bounds(endianness_map, subtype_bits, subtype_bits * 2 - 1);

  const bitvector_typet type =
    adjust_width(bitvector_expr.type(), subtype_bits);

  PRECONDITION(pointer_offset_bits(bitvector_expr.type(), ns).has_value());
  return complex_exprt{
    bv_to_expr(
      extractbits_exprt{bitvector_expr, bounds_real.ub, bounds_real.lb, type},
      complex_type.subtype(),
      endianness_map,
      ns),
    bv_to_expr(
      extractbits_exprt{bitvector_expr, bounds_imag.ub, bounds_imag.lb, type},
      complex_type.subtype(),
      endianness_map,
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
/// \param endianness_map: Endianness map.
/// \return Expression of type \p target_type constructed from sequences of bits
/// from \p bitvector_expr.
static exprt bv_to_expr(
  const exprt &bitvector_expr,
  const typet &target_type,
  const endianness_mapt &endianness_map,
  const namespacet &ns)
{
  PRECONDITION(can_cast_type<bitvector_typet>(bitvector_expr.type()));

  if(target_type.id() == ID_floatbv)
  {
    std::size_t width = to_bitvector_type(bitvector_expr.type()).get_width();
    exprt bv_expr =
      typecast_exprt::conditional_cast(bitvector_expr, bv_typet{width});
    return simplify_expr(
      typecast_exprt::conditional_cast(bv_expr, target_type), ns);
  }
  else if(
    can_cast_type<bitvector_typet>(target_type) ||
    target_type.id() == ID_c_enum || target_type.id() == ID_c_enum_tag ||
    target_type.id() == ID_string)
  {
    return simplify_expr(
      typecast_exprt::conditional_cast(bitvector_expr, target_type), ns);
  }

  if(target_type.id() == ID_struct)
  {
    return bv_to_struct_expr(
      bitvector_expr, to_struct_type(target_type), endianness_map, ns);
  }
  else if(target_type.id() == ID_struct_tag)
  {
    struct_exprt result = bv_to_struct_expr(
      bitvector_expr,
      ns.follow_tag(to_struct_tag_type(target_type)),
      endianness_map,
      ns);
    result.type() = target_type;
    return std::move(result);
  }
  else if(target_type.id() == ID_union)
  {
    return bv_to_union_expr(
      bitvector_expr, to_union_type(target_type), endianness_map, ns);
  }
  else if(target_type.id() == ID_union_tag)
  {
    exprt result = bv_to_union_expr(
      bitvector_expr,
      ns.follow_tag(to_union_tag_type(target_type)),
      endianness_map,
      ns);
    result.type() = target_type;
    return result;
  }
  else if(target_type.id() == ID_array)
  {
    return bv_to_array_expr(
      bitvector_expr, to_array_type(target_type), endianness_map, ns);
  }
  else if(target_type.id() == ID_vector)
  {
    return bv_to_vector_expr(
      bitvector_expr, to_vector_type(target_type), endianness_map, ns);
  }
  else if(target_type.id() == ID_complex)
  {
    return bv_to_complex_expr(
      bitvector_expr, to_complex_type(target_type), endianness_map, ns);
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
  const std::size_t bits_per_byte,
  const namespacet &ns,
  bool unpack_byte_array = false);

/// Build the individual bytes to be used in an update.
/// \param src: Source expression of array or vector type
/// \param lower_bound: First index into \p src to be included in the result
/// \param upper_bound: First index into \p src to be excluded from the result
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: Namespace
/// \return Sequence of bytes.
static exprt::operandst instantiate_byte_array(
  const exprt &src,
  std::size_t lower_bound,
  std::size_t upper_bound,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  PRECONDITION(lower_bound <= upper_bound);

  if(src.id() == ID_array)
  {
    PRECONDITION(upper_bound <= src.operands().size());
    return exprt::operandst{
      src.operands().begin() + narrow_cast<std::ptrdiff_t>(lower_bound),
      src.operands().begin() + narrow_cast<std::ptrdiff_t>(upper_bound)};
  }

  const typet &element_type = src.type().id() == ID_array
                                ? to_array_type(src.type()).element_type()
                                : to_vector_type(src.type()).element_type();
  const typet index_type = src.type().id() == ID_array
                             ? to_array_type(src.type()).index_type()
                             : to_vector_type(src.type()).index_type();
  PRECONDITION(
    can_cast_type<bitvector_typet>(element_type) &&
    to_bitvector_type(element_type).get_width() == bits_per_byte);
  exprt::operandst bytes;
  bytes.reserve(upper_bound - lower_bound);
  for(std::size_t i = lower_bound; i < upper_bound; ++i)
  {
    const index_exprt idx{src, from_integer(i, index_type)};
    bytes.push_back(simplify_expr(idx, ns));
  }
  return bytes;
}

/// Rewrite an array or vector into its individual bytes when no maximum number
/// of bytes is known.
/// \param src: array/vector to unpack
/// \param el_bytes: byte width of array/vector elements
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
/// \return Array expression holding unpacked elements or array comprehension
static exprt unpack_array_vector_no_known_bounds(
  const exprt &src,
  std::size_t el_bytes,
  bool little_endian,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  const typet index_type = src.type().id() == ID_array
                             ? to_array_type(src.type()).index_type()
                             : to_vector_type(src.type()).index_type();

  // TODO we either need a symbol table here or make array comprehensions
  // introduce a scope
  static std::size_t array_comprehension_index_counter = 0;
  ++array_comprehension_index_counter;
  symbol_exprt array_comprehension_index{
    "$array_comprehension_index_a_v" +
      std::to_string(array_comprehension_index_counter),
    index_type};

  index_exprt element{
    src,
    div_exprt{array_comprehension_index, from_integer(el_bytes, index_type)}};

  exprt sub =
    unpack_rec(element, little_endian, {}, {}, bits_per_byte, ns, false);
  exprt::operandst sub_operands =
    instantiate_byte_array(sub, 0, el_bytes, bits_per_byte, ns);

  exprt body = sub_operands.front();
  const mod_exprt offset{
    array_comprehension_index,
    from_integer(el_bytes, array_comprehension_index.type())};
  for(std::size_t i = 1; i < el_bytes; ++i)
  {
    body = if_exprt{
      equal_exprt{offset, from_integer(i, array_comprehension_index.type())},
      sub_operands[i],
      body};
  }

  const exprt array_vector_size = src.type().id() == ID_vector
                                    ? to_vector_type(src.type()).size()
                                    : to_array_type(src.type()).size();

  return array_comprehension_exprt{
    std::move(array_comprehension_index),
    std::move(body),
    array_typet{
      bv_typet{bits_per_byte},
      mult_exprt{
        array_vector_size, from_integer(el_bytes, array_vector_size.type())}}};
}

/// Rewrite an array or vector into its individual bytes.
/// \param src: array/vector to unpack
/// \param src_size: number of elements in \p src, if the array/vector size is
///   constant; if the array/vector size is not constant (and this argument thus
///   not set), \p max_bytes needs to be a known constant value to build an
///   array expression, else we fall back to building an array comprehension
/// \param element_bits: bit width of array/vector elements
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled
///   with nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
/// \return Array expression holding unpacked elements or array comprehension
static exprt unpack_array_vector(
  const exprt &src,
  const optionalt<mp_integer> &src_size,
  const mp_integer &element_bits,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  const std::size_t el_bytes = numeric_cast_v<std::size_t>(
    (element_bits + bits_per_byte - 1) / bits_per_byte);

  if(!src_size.has_value() && !max_bytes.has_value())
  {
    PRECONDITION_WITH_DIAGNOSTICS(
      el_bytes > 0 && element_bits % bits_per_byte == 0,
      "unpacking of arrays with non-byte-aligned elements is not supported");
    return unpack_array_vector_no_known_bounds(
      src, el_bytes, little_endian, bits_per_byte, ns);
  }

  exprt::operandst byte_operands;
  mp_integer first_element = 0;

  // refine the number of elements to extract in case the element width is known
  // and a multiple of bytes; otherwise we will expand the entire array/vector
  optionalt<mp_integer> num_elements = src_size;
  if(element_bits > 0)
  {
    if(!num_elements.has_value())
    {
      // turn bytes into elements, rounding up
      num_elements =
        (*max_bytes * bits_per_byte + element_bits - 1) / element_bits;
    }

    if(offset_bytes.has_value())
    {
      // compute offset as number of elements
      first_element = *offset_bytes * bits_per_byte / element_bits;
      // insert offset_bytes-many zero bytes into the output array
      byte_operands.resize(
        numeric_cast_v<std::size_t>(std::min(
          (*offset_bytes * bits_per_byte -
           ((*offset_bytes * bits_per_byte) % element_bits)) /
            bits_per_byte,
          *num_elements * element_bits / bits_per_byte)),
        from_integer(0, bv_typet{bits_per_byte}));
    }
  }

  // the maximum number of bytes is an upper bound in case the size of the
  // array/vector is unknown; if element_bits was non-zero above this will
  // have been turned into a number of elements already
  if(!num_elements)
    num_elements = *max_bytes;

  const exprt src_simp = simplify_expr(src, ns);
  const typet index_type = src_simp.type().id() == ID_array
                             ? to_array_type(src_simp.type()).index_type()
                             : to_vector_type(src_simp.type()).index_type();

  if(element_bits % bits_per_byte == 0)
  {
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
        element = index_exprt(src_simp, from_integer(i, index_type));
      }

      // recursively unpack each element so that we eventually just have an
      // array of bytes left

      const optionalt<mp_integer> element_max_bytes =
        max_bytes
          ? std::min(mp_integer{el_bytes}, *max_bytes - byte_operands.size())
          : optionalt<mp_integer>{};
      const std::size_t element_max_bytes_int =
        element_max_bytes ? numeric_cast_v<std::size_t>(*element_max_bytes)
                          : el_bytes;

      exprt sub = unpack_rec(
        element, little_endian, {}, element_max_bytes, bits_per_byte, ns, true);
      exprt::operandst sub_operands = instantiate_byte_array(
        sub, 0, element_max_bytes_int, bits_per_byte, ns);
      byte_operands.insert(
        byte_operands.end(), sub_operands.begin(), sub_operands.end());

      if(max_bytes && byte_operands.size() >= *max_bytes)
        break;
    }
  }
  else
  {
    const std::size_t element_bits_int =
      numeric_cast_v<std::size_t>(element_bits);

    exprt::operandst elements;
    for(mp_integer i = *num_elements - 1; i >= first_element; --i)
    {
      if(
        (src_simp.id() == ID_array || src_simp.id() == ID_vector) &&
        i < src_simp.operands().size())
      {
        const std::size_t index_int = numeric_cast_v<std::size_t>(i);
        elements.push_back(typecast_exprt::conditional_cast(
          src_simp.operands()[index_int], bv_typet{element_bits_int}));
      }
      else
      {
        elements.push_back(typecast_exprt::conditional_cast(
          index_exprt(src_simp, from_integer(i, index_type)),
          bv_typet{element_bits_int}));
      }
    }

    const std::size_t merged_bit_width = numeric_cast_v<std::size_t>(
      (*num_elements - first_element) * element_bits);
    if(!little_endian)
      std::reverse(elements.begin(), elements.end());
    concatenation_exprt merged{std::move(elements), bv_typet{merged_bit_width}};

    exprt merged_as_bytes =
      unpack_rec(merged, little_endian, {}, max_bytes, bits_per_byte, ns, true);

    const std::size_t merged_byte_width =
      (merged_bit_width + bits_per_byte - 1) / bits_per_byte;
    const std::size_t max_bytes_int =
      max_bytes.has_value()
        ? std::min(numeric_cast_v<std::size_t>(*max_bytes), merged_byte_width)
        : merged_byte_width;

    exprt::operandst sub_operands = instantiate_byte_array(
      merged_as_bytes, 0, max_bytes_int, bits_per_byte, ns);
    byte_operands.insert(
      byte_operands.end(), sub_operands.begin(), sub_operands.end());
  }

  const std::size_t size = byte_operands.size();
  return array_exprt(
    std::move(byte_operands),
    array_typet{bv_typet{bits_per_byte}, from_integer(size, size_type())});
}

/// Extract bytes from a sequence of bitvector-typed elements.
/// \param bit_fields: operands to concatenate
/// \param total_bits: total bit width of operands
/// \param [out] dest: target to append unpacked bytes to
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled
///   with nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
static void process_bit_fields(
  exprt::operandst &&bit_fields,
  std::size_t total_bits,
  exprt::operandst &dest,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  const concatenation_exprt concatenation{
    std::move(bit_fields), bv_typet{total_bits}};

  exprt sub = unpack_rec(
    concatenation,
    little_endian,
    offset_bytes,
    max_bytes,
    bits_per_byte,
    ns,
    true);

  dest.insert(
    dest.end(),
    std::make_move_iterator(sub.operands().begin()),
    std::make_move_iterator(sub.operands().end()));
}

/// Rewrite a struct-typed expression into its individual bytes.
/// \param src: struct-typed expression to unpack
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled
///   with nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
/// \return array_exprt holding unpacked elements
static array_exprt unpack_struct(
  const exprt &src,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  const struct_typet &struct_type = to_struct_type(ns.follow(src.type()));
  const struct_typet::componentst &components = struct_type.components();

  optionalt<mp_integer> offset_in_member;
  optionalt<mp_integer> max_bytes_left;
  optionalt<std::pair<exprt::operandst, std::size_t>> bit_fields;

  mp_integer member_offset_bits = 0;
  exprt::operandst byte_operands;
  for(auto it = components.begin(); it != components.end(); ++it)
  {
    const auto &comp = *it;
    auto component_bits = pointer_offset_bits(comp.type(), ns);

    // We can only handle a member of unknown width when it is the last member
    // and is byte-aligned. Members of unknown width in the middle would leave
    // us with unknown alignment of subsequent members, and queuing them up as
    // bit fields is not possible either as the total width of the concatenation
    // could not be determined.
    DATA_INVARIANT(
      component_bits.has_value() ||
        (std::next(it) == components.end() && !bit_fields.has_value()),
      "members of non-constant width should come last in a struct");

    member_exprt member(src, comp.get_name(), comp.type());
    if(src.id() == ID_struct)
      simplify(member, ns);

    // Is it a byte-aligned member?
    if(member_offset_bits % bits_per_byte == 0)
    {
      if(bit_fields.has_value())
      {
        process_bit_fields(
          std::move(bit_fields->first),
          bit_fields->second,
          byte_operands,
          little_endian,
          offset_in_member,
          max_bytes_left,
          bits_per_byte,
          ns);
        bit_fields.reset();
      }

      if(offset_bytes.has_value())
      {
        offset_in_member = *offset_bytes - member_offset_bits / bits_per_byte;
        // if the offset is negative, offset_in_member remains unset, which has
        // the same effect as setting it to zero
        if(*offset_in_member < 0)
          offset_in_member.reset();
      }

      if(max_bytes.has_value())
      {
        max_bytes_left = *max_bytes - member_offset_bits / bits_per_byte;
        if(*max_bytes_left < 0)
          break;
      }
    }

    if(
      member_offset_bits % bits_per_byte != 0 ||
      (component_bits.has_value() && *component_bits % bits_per_byte != 0))
    {
      if(!bit_fields.has_value())
        bit_fields = std::make_pair(exprt::operandst{}, std::size_t{0});

      const std::size_t bits_int = numeric_cast_v<std::size_t>(*component_bits);
      bit_fields->first.insert(
        little_endian ? bit_fields->first.begin() : bit_fields->first.end(),
        typecast_exprt::conditional_cast(member, bv_typet{bits_int}));
      bit_fields->second += bits_int;

      member_offset_bits += *component_bits;

      continue;
    }

    INVARIANT(
      !bit_fields.has_value(),
      "all preceding members should have been processed");

    if(
      component_bits.has_value() && offset_in_member.has_value() &&
      *offset_in_member * bits_per_byte >= *component_bits)
    {
      // we won't actually need this component, fill in zeros instead of
      // computing an unpacking
      byte_operands.resize(
        byte_operands.size() +
          numeric_cast_v<std::size_t>(*component_bits / bits_per_byte),
        from_integer(0, bv_typet{bits_per_byte}));
    }
    else
    {
      exprt sub = unpack_rec(
        member,
        little_endian,
        offset_in_member,
        max_bytes_left,
        bits_per_byte,
        ns,
        true);

      byte_operands.insert(
        byte_operands.end(),
        std::make_move_iterator(sub.operands().begin()),
        std::make_move_iterator(sub.operands().end()));
    }

    if(component_bits.has_value())
      member_offset_bits += *component_bits;
  }

  // any remaining bit fields?
  if(bit_fields.has_value())
  {
    process_bit_fields(
      std::move(bit_fields->first),
      bit_fields->second,
      byte_operands,
      little_endian,
      offset_in_member,
      max_bytes_left,
      bits_per_byte,
      ns);
  }

  const std::size_t size = byte_operands.size();
  return array_exprt{
    std::move(byte_operands),
    array_typet{bv_typet{bits_per_byte}, from_integer(size, size_type())}};
}

/// Rewrite a complex_exprt into its individual bytes.
/// \param src: complex-typed expression to unpack
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
/// \return array_exprt holding unpacked elements
static array_exprt unpack_complex(
  const exprt &src,
  bool little_endian,
  const std::size_t bits_per_byte,
  const namespacet &ns)
{
  const complex_typet &complex_type = to_complex_type(src.type());
  const typet &subtype = complex_type.subtype();

  auto subtype_bits = pointer_offset_bits(subtype, ns);
  CHECK_RETURN(subtype_bits.has_value());
  CHECK_RETURN(*subtype_bits % bits_per_byte == 0);

  exprt sub_real = unpack_rec(
    complex_real_exprt{src},
    little_endian,
    mp_integer{0},
    *subtype_bits / bits_per_byte,
    bits_per_byte,
    ns,
    true);
  exprt::operandst byte_operands = std::move(sub_real.operands());

  exprt sub_imag = unpack_rec(
    complex_imag_exprt{src},
    little_endian,
    mp_integer{0},
    *subtype_bits / bits_per_byte,
    bits_per_byte,
    ns,
    true);
  byte_operands.insert(
    byte_operands.end(),
    std::make_move_iterator(sub_imag.operands().begin()),
    std::make_move_iterator(sub_imag.operands().end()));

  const std::size_t size = byte_operands.size();
  return array_exprt{
    std::move(byte_operands),
    array_typet{bv_typet{bits_per_byte}, from_integer(size, size_type())}};
}

/// Rewrite an object into its individual bytes.
/// \param src: object to unpack
/// \param little_endian: true, iff assumed endianness is little-endian
/// \param offset_bytes: if set, bytes prior to this offset will be filled with
///   nil values
/// \param max_bytes: if set, use as upper bound of the number of bytes to
///   unpack
/// \param bits_per_byte: number of bits that make up a byte
/// \param ns: namespace for type lookups
/// \param unpack_byte_array: if true, return unmodified \p src iff it is an
//    array of bytes
/// \return array of bytes in the sequence found in memory
static exprt unpack_rec(
  const exprt &src,
  bool little_endian,
  const optionalt<mp_integer> &offset_bytes,
  const optionalt<mp_integer> &max_bytes,
  const std::size_t bits_per_byte,
  const namespacet &ns,
  bool unpack_byte_array)
{
  if(src.type().id() == ID_array)
  {
    const array_typet &array_type = to_array_type(src.type());
    const typet &subtype = array_type.element_type();

    auto element_bits = pointer_offset_bits(subtype, ns);
    CHECK_RETURN(element_bits.has_value());

    if(
      !unpack_byte_array && *element_bits == bits_per_byte &&
      can_cast_type<bitvector_typet>(subtype))
    {
      return src;
    }

    const auto constant_size_opt = numeric_cast<mp_integer>(array_type.size());
    return unpack_array_vector(
      src,
      constant_size_opt,
      *element_bits,
      little_endian,
      offset_bytes,
      max_bytes,
      bits_per_byte,
      ns);
  }
  else if(src.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(src.type());
    const typet &subtype = vector_type.element_type();

    auto element_bits = pointer_offset_bits(subtype, ns);
    CHECK_RETURN(element_bits.has_value());

    if(
      !unpack_byte_array && *element_bits == bits_per_byte &&
      can_cast_type<bitvector_typet>(subtype))
    {
      return src;
    }

    return unpack_array_vector(
      src,
      numeric_cast_v<mp_integer>(vector_type.size()),
      *element_bits,
      little_endian,
      offset_bytes,
      max_bytes,
      bits_per_byte,
      ns);
  }
  else if(src.type().id() == ID_complex)
  {
    return unpack_complex(src, little_endian, bits_per_byte, ns);
  }
  else if(src.type().id() == ID_struct || src.type().id() == ID_struct_tag)
  {
    return unpack_struct(
      src, little_endian, offset_bytes, max_bytes, bits_per_byte, ns);
  }
  else if(src.type().id() == ID_union || src.type().id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(src.type()));

    const auto widest_member = union_type.find_widest_union_component(ns);

    if(widest_member.has_value())
    {
      member_exprt member{
        src, widest_member->first.get_name(), widest_member->first.type()};
      return unpack_rec(
        member,
        little_endian,
        offset_bytes,
        widest_member->second,
        bits_per_byte,
        ns,
        true);
    }
    else if(!union_type.components().empty())
    {
      member_exprt member{src, union_type.components().front()};
      return unpack_rec(
        member,
        little_endian,
        offset_bytes,
        max_bytes,
        bits_per_byte,
        ns,
        true);
    }
  }
  else if(src.type().id() == ID_pointer)
  {
    return unpack_rec(
      typecast_exprt{src, bv_typet{to_pointer_type(src.type()).get_width()}},
      little_endian,
      offset_bytes,
      max_bytes,
      bits_per_byte,
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
      bits_per_byte,
      ns,
      unpack_byte_array);
  }
  else if(src.is_constant() && src.type().id() == ID_string)
  {
    return unpack_rec(
      string_constantt(to_constant_expr(src).get_value()).to_array_expr(),
      little_endian,
      offset_bytes,
      max_bytes,
      bits_per_byte,
      ns,
      unpack_byte_array);
  }
  else if(src.type().id() != ID_empty)
  {
    // a basic type; we turn that into extractbits while considering
    // endianness
    auto bits_opt = pointer_offset_bits(src.type(), ns);
    DATA_INVARIANT(bits_opt.has_value(), "basic type should have a fixed size");

    const mp_integer total_bits = *bits_opt;
    mp_integer last_bit = total_bits;
    mp_integer bit_offset = 0;

    if(max_bytes.has_value())
    {
      const auto max_bits = *max_bytes * bits_per_byte;
      if(little_endian)
      {
        last_bit = std::min(last_bit, max_bits);
      }
      else
      {
        bit_offset = std::max(mp_integer{0}, last_bit - max_bits);
      }
    }

    auto const src_as_bitvector = typecast_exprt::conditional_cast(
      src, bv_typet{numeric_cast_v<std::size_t>(total_bits)});
    auto const byte_type = bv_typet{bits_per_byte};
    exprt::operandst byte_operands;
    array_typet array_type{
      bv_typet{bits_per_byte}, from_integer(0, size_type())};

    for(; bit_offset < last_bit; bit_offset += bits_per_byte)
    {
      PRECONDITION(
        pointer_offset_bits(src_as_bitvector.type(), ns).has_value());
      extractbits_exprt extractbits(
        src_as_bitvector,
        from_integer(bit_offset + bits_per_byte - 1, array_type.index_type()),
        from_integer(bit_offset, array_type.index_type()),
        byte_type);

      // endianness_mapt should be the point of reference for mapping out
      // endianness, but we need to work on elements here instead of
      // individual bits
      if(little_endian)
        byte_operands.push_back(extractbits);
      else
        byte_operands.insert(byte_operands.begin(), extractbits);
    }

    const std::size_t size = byte_operands.size();
    array_type.size() = from_integer(size, size_type());
    return array_exprt{std::move(byte_operands), std::move(array_type)};
  }

  return array_exprt(
    {}, array_typet{bv_typet{bits_per_byte}, from_integer(0, size_type())});
}

/// Rewrite a byte extraction of an array/vector-typed result to byte extraction
/// of the individual components that make up an \ref array_exprt or
/// \ref vector_exprt.
/// \param src: Original byte extract expression
/// \param unpacked: Byte extraction with root operand expanded into array (via
///   \ref unpack_rec)
/// \param subtype: Array/vector element type
/// \param element_bits: bit width of array/vector elements
/// \param ns: Namespace
/// \return An array or vector expression.
static exprt lower_byte_extract_array_vector(
  const byte_extract_exprt &src,
  const byte_extract_exprt &unpacked,
  const typet &subtype,
  const mp_integer &element_bits,
  const namespacet &ns)
{
  optionalt<std::size_t> num_elements;
  if(src.type().id() == ID_array)
    num_elements = numeric_cast<std::size_t>(to_array_type(src.type()).size());
  else
    num_elements = numeric_cast<std::size_t>(to_vector_type(src.type()).size());

  if(num_elements.has_value())
  {
    exprt::operandst operands;
    // Work around spurious GCC warning about num_elements being uninitialised.
#pragma GCC diagnostic push
#ifndef __clang__
#  pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif
    operands.reserve(*num_elements);
    for(std::size_t i = 0; i < *num_elements; ++i)
#pragma GCC diagnostic pop
    {
      if(element_bits % src.get_bits_per_byte() == 0)
      {
        plus_exprt new_offset(
          unpacked.offset(),
          from_integer(
            i * element_bits / src.get_bits_per_byte(),
            unpacked.offset().type()));

        byte_extract_exprt tmp(unpacked);
        tmp.type() = subtype;
        tmp.offset() = new_offset;

        operands.push_back(lower_byte_extract(tmp, ns));
      }
      else
      {
        const mp_integer first_index =
          i * element_bits / src.get_bits_per_byte();
        const mp_integer last_index =
          ((i + 1) * element_bits + src.get_bits_per_byte() - 1) /
          src.get_bits_per_byte();

        exprt::operandst to_concat;
        to_concat.reserve(
          numeric_cast_v<std::size_t>(last_index - first_index));
        for(mp_integer j = first_index; j < last_index; ++j)
        {
          to_concat.push_back(index_exprt{
            unpacked.op(),
            plus_exprt{
              unpacked.offset(), from_integer(j, unpacked.offset().type())}});
        }

        const std::size_t base = numeric_cast_v<std::size_t>(
          (i * element_bits) % src.get_bits_per_byte());
        const std::size_t last =
          numeric_cast_v<std::size_t>(base + element_bits - 1);
        bv_typet concat_type{src.get_bits_per_byte() * to_concat.size()};
        endianness_mapt endianness_map(
          concat_type, src.id() == ID_byte_extract_little_endian, ns);
        const auto bounds = map_bounds(endianness_map, base, last);
        extractbits_exprt element{
          concatenation_exprt{to_concat, std::move(concat_type)},
          from_integer(bounds.ub, size_type()),
          from_integer(bounds.lb, size_type()),
          subtype};

        operands.push_back(element);
      }
    }

    exprt result;
    if(src.type().id() == ID_array)
      result = array_exprt{std::move(operands), to_array_type(src.type())};
    else
      result = vector_exprt{std::move(operands), to_vector_type(src.type())};

    return simplify_expr(result, ns);
  }

  DATA_INVARIANT(src.type().id() == ID_array, "vectors have constant size");
  const array_typet &array_type = to_array_type(src.type());

  // TODO we either need a symbol table here or make array comprehensions
  // introduce a scope
  static std::size_t array_comprehension_index_counter = 0;
  ++array_comprehension_index_counter;
  symbol_exprt array_comprehension_index{
    "$array_comprehension_index_a" +
      std::to_string(array_comprehension_index_counter),
    array_type.index_type()};

  PRECONDITION_WITH_DIAGNOSTICS(
    element_bits % src.get_bits_per_byte() == 0,
    "byte extracting non-byte-aligned arrays requires constant size");

  plus_exprt new_offset{
    unpacked.offset(),
    typecast_exprt::conditional_cast(
      mult_exprt{
        array_comprehension_index,
        from_integer(
          element_bits / src.get_bits_per_byte(),
          array_comprehension_index.type())},
      unpacked.offset().type())};

  byte_extract_exprt body(unpacked);
  body.type() = subtype;
  body.offset() = std::move(new_offset);

  return array_comprehension_exprt{
    std::move(array_comprehension_index),
    lower_byte_extract(body, ns),
    array_type};
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
  if(!subtype_bits.has_value() || *subtype_bits % src.get_bits_per_byte() != 0)
    return {};

  // offset remains unchanged
  byte_extract_exprt real{unpacked};
  real.type() = subtype;

  const plus_exprt new_offset{
    unpacked.offset(),
    from_integer(
      *subtype_bits / src.get_bits_per_byte(), unpacked.offset().type())};
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

  // determine an upper bound of the last byte we might need
  auto upper_bound_opt = size_of_expr(src.type(), ns);
  if(upper_bound_opt.has_value())
  {
    upper_bound_opt = simplify_expr(
      plus_exprt(
        upper_bound_opt.value(),
        typecast_exprt::conditional_cast(
          src.offset(), upper_bound_opt.value().type())),
      ns);
  }
  else if(src.type().id() == ID_empty)
    upper_bound_opt = from_integer(0, size_type());

  const auto lower_bound_int_opt = numeric_cast<mp_integer>(src.offset());
  const auto upper_bound_int_opt =
    numeric_cast<mp_integer>(upper_bound_opt.value_or(nil_exprt()));

  byte_extract_exprt unpacked(src);
  unpacked.op() = unpack_rec(
    src.op(),
    little_endian,
    lower_bound_int_opt,
    upper_bound_int_opt,
    src.get_bits_per_byte(),
    ns);
  CHECK_RETURN(
    to_bitvector_type(to_type_with_subtype(unpacked.op().type()).subtype())
      .get_width() == src.get_bits_per_byte());

  if(src.type().id() == ID_array || src.type().id() == ID_vector)
  {
    const typet &subtype = to_type_with_subtype(src.type()).subtype();

    auto element_bits = pointer_offset_bits(subtype, ns);
    PRECONDITION_WITH_DIAGNOSTICS(
      element_bits.has_value() && *element_bits >= 1,
      "byte extracting arrays of unknown/zero subtype is not yet implemented");

    return lower_byte_extract_array_vector(
      src, unpacked, subtype, *element_bits, ns);
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
    const struct_typet &struct_type = to_struct_type(ns.follow(src.type()));
    const struct_typet::componentst &components = struct_type.components();

    bool failed = false;
    struct_exprt s({}, src.type());

    for(const auto &comp : components)
    {
      auto component_bits = pointer_offset_bits(comp.type(), ns);

      // the next member would be misaligned, abort
      if(
        !component_bits.has_value() ||
        *component_bits % src.get_bits_per_byte() != 0)
      {
        failed = true;
        break;
      }

      auto member_offset_opt =
        member_offset_expr(struct_type, comp.get_name(), ns);

      if(!member_offset_opt.has_value())
      {
        failed = true;
        break;
      }

      plus_exprt new_offset(
        unpacked.offset(),
        typecast_exprt::conditional_cast(
          member_offset_opt.value(), unpacked.offset().type()));

      byte_extract_exprt tmp(unpacked);
      tmp.type() = comp.type();
      tmp.offset() = new_offset;

      s.add_to_operands(lower_byte_extract(tmp, ns));
    }

    if(!failed)
      return simplify_expr(std::move(s), ns);
  }
  else if(src.type().id() == ID_union || src.type().id() == ID_union_tag)
  {
    const union_typet &union_type = to_union_type(ns.follow(src.type()));

    const auto widest_member = union_type.find_widest_union_component(ns);

    if(widest_member.has_value())
    {
      byte_extract_exprt tmp(unpacked);
      tmp.type() = widest_member->first.type();

      return union_exprt(
        widest_member->first.get_name(),
        lower_byte_extract(tmp, ns),
        src.type());
    }
  }

  const exprt &root = unpacked.op();
  const exprt &offset = unpacked.offset();

  optionalt<typet> subtype;
  optionalt<typet> index_type;
  if(root.type().id() == ID_vector)
  {
    subtype = to_vector_type(root.type()).element_type();
    index_type = to_vector_type(root.type()).index_type();
  }
  else
  {
    subtype = to_array_type(root.type()).element_type();
    index_type = to_array_type(root.type()).index_type();
  }

  auto subtype_bits = pointer_offset_bits(*subtype, ns);

  DATA_INVARIANT(
    subtype_bits.has_value() && *subtype_bits == src.get_bits_per_byte(),
    "offset bits are byte aligned");

  auto size_bits = pointer_offset_bits(unpacked.type(), ns);
  if(!size_bits.has_value())
  {
    auto op0_bits = pointer_offset_bits(unpacked.op().type(), ns);
    // all cases with non-constant width should have been handled above
    DATA_INVARIANT(
      op0_bits.has_value(),
      "the extracted width or the source width must be known");
    size_bits = op0_bits;
  }

  mp_integer num_bytes =
    (*size_bits) / src.get_bits_per_byte() +
    (((*size_bits) % src.get_bits_per_byte() == 0) ? 0 : 1);

  // get 'width'-many bytes, and concatenate
  const std::size_t width_bytes = numeric_cast_v<std::size_t>(num_bytes);
  exprt::operandst op;
  op.reserve(width_bytes);

  for(std::size_t i = 0; i < width_bytes; i++)
  {
    // the most significant byte comes first in the concatenation!
    std::size_t offset_int = little_endian ? (width_bytes - i - 1) : i;

    plus_exprt offset_i{
      from_integer(offset_int, *index_type),
      typecast_exprt::conditional_cast(offset, *index_type)};
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

  if(width_bytes == 1)
  {
    return simplify_expr(
      typecast_exprt::conditional_cast(op.front(), src.type()), ns);
  }
  else // width_bytes>=2
  {
    concatenation_exprt concatenation(
      std::move(op),
      adjust_width(*subtype, width_bytes * src.get_bits_per_byte()));

    endianness_mapt map(concatenation.type(), little_endian, ns);
    return bv_to_expr(concatenation, src.type(), map, ns);
  }
}

static exprt lower_byte_update(
  const byte_update_exprt &src,
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns);

/// Apply a byte update \p src to an array/vector of bytes using the byte-array
/// typed expression \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: Constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array comprehension reflecting all updates.
static exprt lower_byte_update_byte_array_vector_non_const(
  const byte_update_exprt &src,
  const typet &subtype,
  const exprt &value_as_byte_array,
  const exprt &non_const_update_bound,
  const namespacet &ns)
{
  // TODO we either need a symbol table here or make array comprehensions
  // introduce a scope
  static std::size_t array_comprehension_index_counter = 0;
  ++array_comprehension_index_counter;
  symbol_exprt array_comprehension_index{
    "$array_comprehension_index_u_a_v" +
      std::to_string(array_comprehension_index_counter),
    to_array_type(src.type()).index_type()};

  binary_predicate_exprt lower_bound{
    typecast_exprt::conditional_cast(
      array_comprehension_index, src.offset().type()),
    ID_lt,
    src.offset()};
  binary_predicate_exprt upper_bound{
    typecast_exprt::conditional_cast(
      array_comprehension_index, non_const_update_bound.type()),
    ID_ge,
    plus_exprt{
      typecast_exprt::conditional_cast(
        src.offset(), non_const_update_bound.type()),
      non_const_update_bound}};

  PRECONDITION(
    src.id() == ID_byte_update_little_endian ||
    src.id() == ID_byte_update_big_endian);
  const bool little_endian = src.id() == ID_byte_update_little_endian;
  endianness_mapt map(
    to_array_type(value_as_byte_array.type()).element_type(),
    little_endian,
    ns);
  if_exprt array_comprehension_body{
    or_exprt{std::move(lower_bound), std::move(upper_bound)},
    index_exprt{src.op(), array_comprehension_index},
    bv_to_expr(
      index_exprt{
        value_as_byte_array,
        minus_exprt{
          array_comprehension_index,
          typecast_exprt::conditional_cast(
            src.offset(), array_comprehension_index.type())}},
      subtype,
      map,
      ns)};

  return simplify_expr(
    array_comprehension_exprt{
      array_comprehension_index,
      std::move(array_comprehension_body),
      to_array_type(src.type())},
    ns);
}

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
  PRECONDITION(
    src.id() == ID_byte_update_little_endian ||
    src.id() == ID_byte_update_big_endian);
  const bool little_endian = src.id() == ID_byte_update_little_endian;

  const typet index_type = src.type().id() == ID_array
                             ? to_array_type(src.type()).index_type()
                             : to_vector_type(src.type()).index_type();

  // apply 'array-update-with' num_elements times
  exprt result = src.op();

  for(std::size_t i = 0; i < value_as_byte_array.operands().size(); ++i)
  {
    const exprt &element = value_as_byte_array.operands()[i];

    exprt where = simplify_expr(
      plus_exprt{
        typecast_exprt::conditional_cast(src.offset(), index_type),
        from_integer(i, index_type)},
      ns);

    // skip elements that wouldn't change (skip over typecasts as we might have
    // some signed/unsigned char conversions)
    const exprt &e = skip_typecast(element);
    if(e.id() == ID_index)
    {
      const index_exprt &index_expr = to_index_expr(e);
      if(index_expr.array() == src.op() && index_expr.index() == where)
        continue;
    }

    endianness_mapt map(element.type(), little_endian, ns);
    exprt update_value = bv_to_expr(element, subtype, map, ns);
    if(non_const_update_bound.has_value())
    {
      update_value = if_exprt{
        binary_predicate_exprt{
          from_integer(i, non_const_update_bound->type()),
          ID_lt,
          *non_const_update_bound},
        update_value,
        index_exprt{src.op(), where}};
    }

    if(result.id() != ID_with)
      result = with_exprt{result, std::move(where), std::move(update_value)};
    else
      result.add_to_operands(std::move(where), std::move(update_value));
  }

  return simplify_expr(std::move(result), ns);
}

/// Apply a byte update \p src to an array/vector typed operand, using the byte
/// array \p value_as_byte_array as update value, which has non-constant size.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param subtype_size: Size (in bytes) of \p subtype
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: Constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param initial_bytes: Number of bytes from \p value_as_byte_array to use to
///   update the array/vector element at \p first_index
/// \param first_index: Lowest index into the target array/vector of the update
/// \param first_update_value: Combined value of partially old and updated bytes
///   to use at \p first_index
/// \param ns: Namespace
/// \return Array comprehension reflecting all updates.
static exprt lower_byte_update_array_vector_unbounded(
  const byte_update_exprt &src,
  const typet &subtype,
  const exprt &subtype_size,
  const exprt &value_as_byte_array,
  const exprt &non_const_update_bound,
  const exprt &initial_bytes,
  const exprt &first_index,
  const exprt &first_update_value,
  const namespacet &ns)
{
  const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                    ? ID_byte_extract_little_endian
                                    : ID_byte_extract_big_endian;

  // TODO we either need a symbol table here or make array comprehensions
  // introduce a scope
  static std::size_t array_comprehension_index_counter = 0;
  ++array_comprehension_index_counter;
  symbol_exprt array_comprehension_index{
    "$array_comprehension_index_u_a_v_u" +
      std::to_string(array_comprehension_index_counter),
    to_array_type(src.type()).index_type()};

  // all arithmetic uses offset/index types
  PRECONDITION(array_comprehension_index.type() == src.offset().type());
  PRECONDITION(subtype_size.type() == src.offset().type());
  PRECONDITION(initial_bytes.type() == src.offset().type());
  PRECONDITION(first_index.type() == src.offset().type());

  // the bound from where updates start
  binary_predicate_exprt lower_bound{
    typecast_exprt::conditional_cast(
      array_comprehension_index, first_index.type()),
    ID_lt,
    first_index};

  // The actual value of updates other than at the start or end
  plus_exprt offset_expr{
    initial_bytes,
    mult_exprt{
      subtype_size,
      minus_exprt{
        typecast_exprt::conditional_cast(
          array_comprehension_index, first_index.type()),
        plus_exprt{first_index, from_integer(1, first_index.type())}}}};
  exprt update_value = lower_byte_extract(
    byte_extract_exprt{
      extract_opcode,
      value_as_byte_array,
      std::move(offset_expr),
      src.get_bits_per_byte(),
      subtype},
    ns);

  // The number of target array/vector elements being replaced, not including
  // a possible partial update at the end of the updated range, which is handled
  // below: (non_const_update_bound + (subtype_size - 1)) / subtype_size to
  // round up to the nearest multiple of subtype_size.
  div_exprt updated_elements{
    plus_exprt{
      typecast_exprt::conditional_cast(
        non_const_update_bound, subtype_size.type()),
      minus_exprt{subtype_size, from_integer(1, subtype_size.type())}},
    subtype_size};

  // The last element to be updated: first_index + updated_elements - 1
  plus_exprt last_index{
    first_index,
    minus_exprt{
      std::move(updated_elements), from_integer(1, first_index.type())}};

  // The size of a partial update at the end of the updated range, may be zero.
  mod_exprt tail_size{
    typecast_exprt::conditional_cast(
      minus_exprt{
        typecast_exprt::conditional_cast(
          non_const_update_bound, initial_bytes.type()),
        initial_bytes},
      subtype_size.type()),
    subtype_size};

  // The bound where updates end, which is conditional on the partial update
  // being empty.
  binary_predicate_exprt upper_bound{
    typecast_exprt::conditional_cast(
      array_comprehension_index, last_index.type()),
    ID_ge,
    if_exprt{
      equal_exprt{tail_size, from_integer(0, tail_size.type())},
      last_index,
      plus_exprt{last_index, from_integer(1, last_index.type())}}};

  // The actual value of a partial update at the end.
  exprt last_update_value = lower_byte_update(
    byte_update_exprt{
      src.id(),
      index_exprt{src.op(), last_index},
      unary_minus_exprt{mult_exprt{
        typecast_exprt::conditional_cast(last_index, subtype_size.type()),
        subtype_size}},
      value_as_byte_array,
      src.get_bits_per_byte()},
    ns);

  if_exprt array_comprehension_body{
    or_exprt{std::move(lower_bound), std::move(upper_bound)},
    index_exprt{src.op(), array_comprehension_index},
    if_exprt{
      equal_exprt{
        typecast_exprt::conditional_cast(
          array_comprehension_index, first_index.type()),
        first_index},
      first_update_value,
      if_exprt{
        equal_exprt{
          typecast_exprt::conditional_cast(
            array_comprehension_index, last_index.type()),
          last_index},
        std::move(last_update_value),
        std::move(update_value)}}};

  return simplify_expr(
    array_comprehension_exprt{
      array_comprehension_index,
      std::move(array_comprehension_body),
      to_array_type(src.type())},
    ns);
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
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  // do all arithmetic below using index/offset types - the array theory
  // back-end is really picky about indices having the same type
  auto subtype_size_opt = size_of_expr(subtype, ns);
  CHECK_RETURN(subtype_size_opt.has_value());

  const exprt subtype_size = simplify_expr(
    typecast_exprt::conditional_cast(
      subtype_size_opt.value(), src.offset().type()),
    ns);

  // compute the index of the first element of the array/vector that may be
  // updated
  PRECONDITION(
    src.offset().type() == to_array_type(src.op().type()).index_type());
  exprt first_index = div_exprt{src.offset(), subtype_size};
  simplify(first_index, ns);

  // compute the offset within that first element
  const exprt update_offset = mod_exprt{src.offset(), subtype_size};

  // compute the number of bytes (from the update value) that are going to be
  // consumed for updating the first element
  const exprt update_size =
    from_integer(value_as_byte_array.operands().size(), subtype_size.type());
  exprt initial_bytes = minus_exprt{subtype_size, update_offset};
  exprt update_bound;
  if(non_const_update_bound.has_value())
  {
    update_bound = typecast_exprt::conditional_cast(
      *non_const_update_bound, subtype_size.type());
  }
  else
  {
    DATA_INVARIANT(
      value_as_byte_array.id() == ID_array,
      "value should be an array expression if the update bound is constant");
    update_bound = update_size;
  }
  initial_bytes = if_exprt{
    binary_predicate_exprt{initial_bytes, ID_lt, update_bound},
    initial_bytes,
    update_bound};
  simplify(initial_bytes, ns);

  // encode the first update: update the original element at first_index (the
  // actual update will only be initial_bytes-many bytes from
  // value_as_byte_array)
  exprt first_update_value = lower_byte_update(
    byte_update_exprt{
      src.id(),
      index_exprt{src.op(), first_index},
      update_offset,
      value_as_byte_array,
      src.get_bits_per_byte()},
    ns);

  if(value_as_byte_array.id() != ID_array)
  {
    return lower_byte_update_array_vector_unbounded(
      src,
      subtype,
      subtype_size,
      value_as_byte_array,
      *non_const_update_bound,
      initial_bytes,
      first_index,
      first_update_value,
      ns);
  }

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

  with_exprt result{src.op(), first_index, first_update_value};

  auto lower_byte_update_array_vector_non_const_one_element =
    [&src,
     &first_index,
     &initial_bytes,
     &subtype_size,
     &value_as_byte_array,
     &ns,
     &result](std::size_t i) -> void {
    exprt where = simplify_expr(
      plus_exprt{first_index, from_integer(i, first_index.type())}, ns);

    exprt neg_offset_expr = simplify_expr(
      unary_minus_exprt{plus_exprt{
        initial_bytes,
        mult_exprt{subtype_size, from_integer(i - 1, subtype_size.type())}}},
      ns);

    exprt element = lower_byte_update(
      byte_update_exprt{
        src.id(),
        index_exprt{src.op(), where},
        neg_offset_expr,
        value_as_byte_array,
        src.get_bits_per_byte()},
      ns);

    result.add_to_operands(std::move(where), std::move(element));
  };

  std::size_t i = 1;
  for(; offset + step_size <= value_as_byte_array.operands().size();
      offset += step_size, ++i)
  {
    lower_byte_update_array_vector_non_const_one_element(i);
  }

  // do the tail
  if(offset < value_as_byte_array.operands().size())
    lower_byte_update_array_vector_non_const_one_element(i);

  return simplify_expr(std::move(result), ns);
}

/// Byte update a struct/array/vector element.
/// \param src: Original byte-update expression
/// \param offset_bits: Offset in \p src expressed as bits
/// \param element_to_update: struct/array/vector element
/// \param subtype_bits: Bit width of \p element_to_update
/// \param bits_already_set: Number of bits in the original target object that
///   have been updated already
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array/vector expression reflecting all updates.
static exprt lower_byte_update_single_element(
  const byte_update_exprt &src,
  const mp_integer &offset_bits,
  const exprt &element_to_update,
  const mp_integer &subtype_bits,
  const mp_integer &bits_already_set,
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  // We need to take one or more bytes from value_as_byte_array to modify the
  // target element. We need to compute:
  // - The position in value_as_byte_array to take bytes from: If subtype_bits
  // is less than the size of a byte, then multiple struct/array/vector elements
  // will need to be updated using the same byte.
  std::size_t first = 0;
  // - An upper bound on the number of bytes required from value_as_byte_array.
  mp_integer update_elements =
    (subtype_bits + src.get_bits_per_byte() - 1) / src.get_bits_per_byte();
  // - The offset into the target element: If subtype_bits is greater or equal
  // to the size of a byte, then there may be an offset into the target element
  // that needs to be taken into account, and multiple bytes will be required.
  mp_integer offset_bits_in_target_element = offset_bits - bits_already_set;

  if(offset_bits_in_target_element < 0)
  {
    INVARIANT(
      value_as_byte_array.id() != ID_array ||
        value_as_byte_array.operands().size() * src.get_bits_per_byte() >
          -offset_bits_in_target_element,
      "indices past the update should be handled below");
    first += numeric_cast_v<std::size_t>(
      -offset_bits_in_target_element / src.get_bits_per_byte());
    offset_bits_in_target_element +=
      (-offset_bits_in_target_element / src.get_bits_per_byte()) *
      src.get_bits_per_byte();
    if(offset_bits_in_target_element < 0)
      ++update_elements;
  }
  else
  {
    update_elements -= offset_bits_in_target_element / src.get_bits_per_byte();
    INVARIANT(
      update_elements > 0, "indices before the update should be handled above");
  }

  std::size_t end = first + numeric_cast_v<std::size_t>(update_elements);
  if(value_as_byte_array.id() == ID_array)
    end = std::min(end, value_as_byte_array.operands().size());
  exprt::operandst update_values = instantiate_byte_array(
    value_as_byte_array, first, end, src.get_bits_per_byte(), ns);
  const std::size_t update_size = update_values.size();
  const exprt update_size_expr = from_integer(update_size, size_type());
  const array_typet update_type{
    bv_typet{src.get_bits_per_byte()}, update_size_expr};

  // each case below will set "new_value" as appropriate
  exprt new_value;

  if(
    offset_bits_in_target_element >= 0 &&
    offset_bits_in_target_element % src.get_bits_per_byte() == 0)
  {
    new_value = array_exprt{update_values, update_type};
  }
  else
  {
    if(src.id() == ID_byte_update_little_endian)
      std::reverse(update_values.begin(), update_values.end());
    if(offset_bits_in_target_element < 0)
    {
      if(src.id() == ID_byte_update_little_endian)
      {
        new_value = lshr_exprt{
          concatenation_exprt{
            update_values, bv_typet{update_size * src.get_bits_per_byte()}},
          numeric_cast_v<std::size_t>(-offset_bits_in_target_element)};
      }
      else
      {
        new_value = shl_exprt{
          concatenation_exprt{
            update_values, bv_typet{update_size * src.get_bits_per_byte()}},
          numeric_cast_v<std::size_t>(-offset_bits_in_target_element)};
      }
    }
    else
    {
      const std::size_t offset_bits_int =
        numeric_cast_v<std::size_t>(offset_bits_in_target_element);
      const std::size_t subtype_bits_int =
        numeric_cast_v<std::size_t>(subtype_bits);

      extractbits_exprt bits_to_keep{
        element_to_update,
        subtype_bits_int - 1,
        subtype_bits_int - offset_bits_int,
        bv_typet{offset_bits_int}};
      new_value = concatenation_exprt{
        bits_to_keep,
        extractbits_exprt{
          concatenation_exprt{
            update_values, bv_typet{update_size * src.get_bits_per_byte()}},
          update_size * src.get_bits_per_byte() - 1,
          offset_bits_int,
          bv_typet{update_size * src.get_bits_per_byte() - offset_bits_int}},
        bv_typet{update_size * src.get_bits_per_byte()}};
    }

    const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                      ? ID_byte_extract_little_endian
                                      : ID_byte_extract_big_endian;

    const byte_extract_exprt byte_extract_expr{
      extract_opcode,
      new_value,
      from_integer(0, src.offset().type()),
      src.get_bits_per_byte(),
      update_type};

    new_value = lower_byte_extract(byte_extract_expr, ns);

    offset_bits_in_target_element = 0;
  }

  // With an upper bound on the size of the update established, construct the
  // actual update expression. If the exact size of the update is unknown,
  // make the size expression conditional.
  const byte_update_exprt bu{
    src.id(),
    element_to_update,
    from_integer(
      offset_bits_in_target_element / src.get_bits_per_byte(),
      src.offset().type()),
    new_value,
    src.get_bits_per_byte()};

  optionalt<exprt> update_bound;
  if(non_const_update_bound.has_value())
  {
    // The size of the update is not constant, and thus is to be symbolically
    // bound; first see how many bytes we have left in the update:
    // non_const_update_bound > first ? non_const_update_bound - first: 0
    const exprt remaining_update_bytes = typecast_exprt::conditional_cast(
      if_exprt{
        binary_predicate_exprt{
          *non_const_update_bound,
          ID_gt,
          from_integer(first, non_const_update_bound->type())},
        minus_exprt{
          *non_const_update_bound,
          from_integer(first, non_const_update_bound->type())},
        from_integer(0, non_const_update_bound->type())},
      size_type());
    // Now take the minimum of update-bytes-left and the previously computed
    // size of the element to be updated:
    update_bound = simplify_expr(
      if_exprt{
        binary_predicate_exprt{update_size_expr, ID_lt, remaining_update_bytes},
        update_size_expr,
        remaining_update_bytes},
      ns);
  }

  return lower_byte_update(bu, new_value, update_bound, ns);
}

/// Apply a byte update \p src to an array/vector typed operand using the byte
/// array \p value_as_byte_array as update value.
/// \param src: Original byte-update expression
/// \param subtype: Array/vector element type
/// \param subtype_bits: Bit width of \p subtype
/// \param value_as_byte_array: Update value as an array of bytes
/// \param non_const_update_bound: If set, (symbolically) constrain updates such
///   as to at most update \p non_const_update_bound elements
/// \param ns: Namespace
/// \return Array/vector expression reflecting all updates.
static exprt lower_byte_update_array_vector(
  const byte_update_exprt &src,
  const typet &subtype,
  const optionalt<mp_integer> &subtype_bits,
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  const bool is_array = src.type().id() == ID_array;
  exprt size;
  typet index_type;
  if(is_array)
  {
    size = to_array_type(src.type()).size();
    index_type = to_array_type(src.type()).index_type();
  }
  else
  {
    size = to_vector_type(src.type()).size();
    index_type = to_vector_type(src.type()).index_type();
  }

  // fall back to bytewise updates in all non-constant or dubious cases
  if(
    !size.is_constant() || !src.offset().is_constant() ||
    !subtype_bits.has_value() || value_as_byte_array.id() != ID_array)
  {
    return lower_byte_update_array_vector_non_const(
      src, subtype, value_as_byte_array, non_const_update_bound, ns);
  }

  std::size_t num_elements =
    numeric_cast_v<std::size_t>(to_constant_expr(size));
  mp_integer offset_bits =
    numeric_cast_v<mp_integer>(to_constant_expr(src.offset())) *
    src.get_bits_per_byte();

  exprt::operandst elements;
  elements.reserve(num_elements);

  std::size_t i = 0;
  // copy the prefix not affected by the update
  for(; i < num_elements && (i + 1) * *subtype_bits <= offset_bits; ++i)
    elements.push_back(index_exprt{src.op(), from_integer(i, index_type)});

  // the modified elements
  for(;
      i < num_elements &&
      i * *subtype_bits < offset_bits + value_as_byte_array.operands().size() *
                                          src.get_bits_per_byte();
      ++i)
  {
    elements.push_back(lower_byte_update_single_element(
      src,
      offset_bits,
      index_exprt{src.op(), from_integer(i, index_type)},
      *subtype_bits,
      i * *subtype_bits,
      value_as_byte_array,
      non_const_update_bound,
      ns));
  }

  // copy the tail not affected by the update
  for(; i < num_elements; ++i)
    elements.push_back(index_exprt{src.op(), from_integer(i, index_type)});

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
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  exprt::operandst elements;
  elements.reserve(struct_type.components().size());

  mp_integer member_offset_bits = 0;
  for(const auto &comp : struct_type.components())
  {
    auto element_width = pointer_offset_bits(comp.type(), ns);

    // compute the update offset relative to this struct member - will be
    // negative if we are already in the middle of the update or beyond it
    exprt offset = simplify_expr(
      minus_exprt{
        mult_exprt{
          src.offset(),
          from_integer(src.get_bits_per_byte(), src.offset().type())},
        from_integer(member_offset_bits, src.offset().type())},
      ns);
    auto offset_bits = numeric_cast<mp_integer>(offset);
    if(!offset_bits.has_value() || !element_width.has_value())
    {
      // The offset to update is not constant, either because the original
      // offset in src never was, or because a struct member has an unknown
      // offset. Abort the attempt to update individual struct members and
      // instead turn the operand-to-be-updated into a byte array, which we know
      // how to update even if the offset is non-constant.
      const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                        ? ID_byte_extract_little_endian
                                        : ID_byte_extract_big_endian;

      auto src_size_opt = size_of_expr(src.type(), ns);
      CHECK_RETURN(src_size_opt.has_value());

      const byte_extract_exprt byte_extract_expr{
        extract_opcode,
        src.op(),
        from_integer(0, src.offset().type()),
        src.get_bits_per_byte(),
        array_typet{bv_typet{src.get_bits_per_byte()}, src_size_opt.value()}};

      byte_update_exprt bu = src;
      bu.set_op(lower_byte_extract(byte_extract_expr, ns));
      bu.type() = bu.op().type();

      return lower_byte_extract(
        byte_extract_exprt{
          extract_opcode,
          lower_byte_update(
            bu, value_as_byte_array, non_const_update_bound, ns),
          from_integer(0, src.offset().type()),
          src.get_bits_per_byte(),
          src.type()},
        ns);
    }

    exprt member = member_exprt{src.op(), comp.get_name(), comp.type()};

    // we don't need to update anything when
    // 1) the update offset is greater than the end of this member (thus the
    // relative offset is greater than this element) or
    // 2) the update offset plus the size of the update is less than the member
    // offset
    if(
      *offset_bits >= *element_width ||
      (value_as_byte_array.id() == ID_array && *offset_bits < 0 &&
       -*offset_bits >=
         value_as_byte_array.operands().size() * src.get_bits_per_byte()))
    {
      elements.push_back(member);
      member_offset_bits += *element_width;
      continue;
    }

    elements.push_back(lower_byte_update_single_element(
      src,
      *offset_bits + member_offset_bits,
      member,
      *element_width,
      member_offset_bits,
      value_as_byte_array,
      non_const_update_bound,
      ns));

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
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  const auto widest_member = union_type.find_widest_union_component(ns);

  PRECONDITION_WITH_DIAGNOSTICS(
    widest_member.has_value(),
    "lower_byte_update of union of unknown size is not supported");

  byte_update_exprt bu = src;
  bu.set_op(member_exprt{
    src.op(), widest_member->first.get_name(), widest_member->first.type()});
  bu.type() = widest_member->first.type();

  return union_exprt{
    widest_member->first.get_name(),
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
  const exprt &value_as_byte_array,
  const optionalt<exprt> &non_const_update_bound,
  const namespacet &ns)
{
  if(src.type().id() == ID_array || src.type().id() == ID_vector)
  {
    optionalt<typet> subtype;
    if(src.type().id() == ID_vector)
      subtype = to_vector_type(src.type()).element_type();
    else
      subtype = to_array_type(src.type()).element_type();

    auto element_width = pointer_offset_bits(*subtype, ns);

    if(element_width.has_value() && *element_width == src.get_bits_per_byte())
    {
      if(value_as_byte_array.id() != ID_array)
      {
        DATA_INVARIANT(
          non_const_update_bound.has_value(),
          "constant update bound should yield an array expression");
        return lower_byte_update_byte_array_vector_non_const(
          src, *subtype, value_as_byte_array, *non_const_update_bound, ns);
      }

      return lower_byte_update_byte_array_vector(
        src,
        *subtype,
        to_array_expr(value_as_byte_array),
        non_const_update_bound,
        ns);
    }
    else
    {
      return lower_byte_update_array_vector(
        src,
        *subtype,
        element_width,
        value_as_byte_array,
        non_const_update_bound,
        ns);
    }
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
    const std::size_t type_bits = numeric_cast_v<std::size_t>(*type_width);

    exprt::operandst update_bytes;
    if(value_as_byte_array.id() == ID_array)
      update_bytes = value_as_byte_array.operands();
    else
    {
      update_bytes = instantiate_byte_array(
        value_as_byte_array,
        0,
        (type_bits + src.get_bits_per_byte() - 1) / src.get_bits_per_byte(),
        src.get_bits_per_byte(),
        ns);
    }

    const std::size_t update_size_bits =
      update_bytes.size() * src.get_bits_per_byte();
    const std::size_t bit_width = std::max(type_bits, update_size_bits);

    const bool is_little_endian = src.id() == ID_byte_update_little_endian;

    exprt val_before =
      typecast_exprt::conditional_cast(src.op(), bv_typet{type_bits});
    if(bit_width > type_bits)
    {
      val_before = concatenation_exprt{
        from_integer(0, bv_typet{bit_width - type_bits}),
        val_before,
        bv_typet{bit_width}};

      if(!is_little_endian)
        to_concatenation_expr(val_before)
          .op0()
          .swap(to_concatenation_expr(val_before).op1());
    }

    if(non_const_update_bound.has_value())
    {
      const exprt src_as_bytes = unpack_rec(
        val_before,
        src.id() == ID_byte_update_little_endian,
        mp_integer{0},
        mp_integer{update_bytes.size()},
        src.get_bits_per_byte(),
        ns);
      CHECK_RETURN(src_as_bytes.id() == ID_array);
      CHECK_RETURN(src_as_bytes.operands().size() == update_bytes.size());
      for(std::size_t i = 0; i < update_bytes.size(); ++i)
      {
        update_bytes[i] = if_exprt{
          binary_predicate_exprt{
            from_integer(i, non_const_update_bound->type()),
            ID_lt,
            *non_const_update_bound},
          update_bytes[i],
          src_as_bytes.operands()[i]};
      }
    }

    // build mask
    exprt mask;
    if(is_little_endian)
      mask = from_integer(power(2, update_size_bits) - 1, bv_typet{bit_width});
    else
    {
      mask = from_integer(
        power(2, bit_width) - power(2, bit_width - update_size_bits),
        bv_typet{bit_width});
    }

    const typet &offset_type = src.offset().type();
    mult_exprt offset_in_bits{
      src.offset(), from_integer(src.get_bits_per_byte(), offset_type)};

    const binary_predicate_exprt offset_ge_zero{
      offset_in_bits, ID_ge, from_integer(0, offset_type)};

    if_exprt mask_shifted{
      offset_ge_zero,
      shl_exprt{mask, offset_in_bits},
      lshr_exprt{mask, unary_minus_exprt{offset_in_bits}}};
    if(!is_little_endian)
    {
      mask_shifted.true_case().swap(mask_shifted.false_case());
      to_shift_expr(mask_shifted.true_case())
        .distance()
        .swap(to_shift_expr(mask_shifted.false_case()).distance());
    }

    // original_bits &= ~mask
    bitand_exprt bitand_expr{val_before, bitnot_exprt{mask_shifted}};

    // concatenate and zero-extend the value
    concatenation_exprt value{update_bytes, bv_typet{update_size_bits}};
    if(is_little_endian)
      std::reverse(value.operands().begin(), value.operands().end());

    exprt zero_extended;
    if(bit_width > update_size_bits)
    {
      zero_extended = concatenation_exprt{
        from_integer(0, bv_typet{bit_width - update_size_bits}),
        value,
        bv_typet{bit_width}};

      if(!is_little_endian)
        to_concatenation_expr(zero_extended)
          .op0()
          .swap(to_concatenation_expr(zero_extended).op1());
    }
    else
      zero_extended = value;

    // shift the value
    if_exprt value_shifted{
      offset_ge_zero,
      shl_exprt{zero_extended, offset_in_bits},
      lshr_exprt{zero_extended, unary_minus_exprt{offset_in_bits}}};
    if(!is_little_endian)
    {
      value_shifted.true_case().swap(value_shifted.false_case());
      to_shift_expr(value_shifted.true_case())
        .distance()
        .swap(to_shift_expr(value_shifted.false_case()).distance());
    }

    // original_bits |= newvalue
    bitor_exprt bitor_expr{bitand_expr, value_shifted};

    if(bit_width > type_bits)
    {
      endianness_mapt endianness_map(
        bitor_expr.type(), src.id() == ID_byte_update_little_endian, ns);
      const auto bounds = map_bounds(endianness_map, 0, type_bits - 1);

      PRECONDITION(pointer_offset_bits(bitor_expr.type(), ns).has_value());
      return simplify_expr(
        typecast_exprt::conditional_cast(
          extractbits_exprt{
            bitor_expr, bounds.ub, bounds.lb, bv_typet{type_bits}},
          src.type()),
        ns);
    }

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
  optionalt<exprt> non_const_update_bound;
  // update value, may require extension to full bytes
  exprt update_value = src.value();
  auto update_size_expr_opt = size_of_expr(update_value.type(), ns);
  CHECK_RETURN(update_size_expr_opt.has_value());
  simplify(update_size_expr_opt.value(), ns);

  const irep_idt extract_opcode = src.id() == ID_byte_update_little_endian
                                    ? ID_byte_extract_little_endian
                                    : ID_byte_extract_big_endian;
  const std::size_t bits_per_byte = src.get_bits_per_byte();

  if(!update_size_expr_opt.value().is_constant())
    non_const_update_bound = *update_size_expr_opt;
  else
  {
    auto update_bits = pointer_offset_bits(update_value.type(), ns);
    // If the following invariant fails, then the type was only found to be
    // constant via simplification. Such instances should be fixed at the place
    // introducing these constant-but-not-constant_exprt type sizes.
    DATA_INVARIANT(
      update_bits.has_value(), "constant size-of should imply fixed bit width");
    const size_t update_bits_int = numeric_cast_v<size_t>(*update_bits);

    if(update_bits_int % bits_per_byte != 0)
    {
      DATA_INVARIANT(
        can_cast_type<bitvector_typet>(update_value.type()),
        "non-byte aligned type expected to be a bitvector type");
      const byte_extract_exprt overlapping_byte_extract{
        extract_opcode,
        src.op(),
        simplify_expr(
          plus_exprt{
            src.offset(),
            from_integer(update_bits_int / bits_per_byte, src.offset().type())},
          ns),
        src.get_bits_per_byte(),
        bv_typet{bits_per_byte}};
      const exprt overlapping_byte =
        lower_byte_extract(overlapping_byte_extract, ns);

      size_t n_extra_bits = bits_per_byte - update_bits_int % bits_per_byte;
      extractbits_exprt extra_bits{
        overlapping_byte, n_extra_bits - 1, 0, bv_typet{n_extra_bits}};

      update_value = concatenation_exprt{
        typecast_exprt::conditional_cast(
          update_value, bv_typet{update_bits_int}),
        extra_bits,
        adjust_width(update_value.type(), update_bits_int + n_extra_bits)};
    }
    else
    {
      update_size_expr_opt = from_integer(
        update_bits_int / bits_per_byte, update_size_expr_opt->type());
    }
  }

  const byte_extract_exprt byte_extract_expr{
    extract_opcode,
    update_value,
    from_integer(0, src.offset().type()),
    src.get_bits_per_byte(),
    array_typet{bv_typet{bits_per_byte}, *update_size_expr_opt}};

  const exprt value_as_byte_array = lower_byte_extract(byte_extract_expr, ns);

  exprt result =
    lower_byte_update(src, value_as_byte_array, non_const_update_bound, ns);
  return result;
}

exprt lower_byte_operators(const exprt &src, const namespacet &ns)
{
  exprt tmp = src;

  // destroys any sharing, should use hash table
  Forall_operands(it, tmp)
  {
    *it = lower_byte_operators(*it, ns);
  }

  if(
    src.id() == ID_byte_update_little_endian ||
    src.id() == ID_byte_update_big_endian)
  {
    return lower_byte_update(to_byte_update_expr(tmp), ns);
  }
  else if(
    src.id() == ID_byte_extract_little_endian ||
    src.id() == ID_byte_extract_big_endian)
  {
    return lower_byte_extract(to_byte_extract_expr(tmp), ns);
  }
  else
    return tmp;
}
