/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#include "pointer_offset_size.h"

#include "arith_tools.h"
#include "base_type.h"
#include "byte_operators.h"
#include "c_types.h"
#include "invariant.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "ssa_expr.h"
#include "std_expr.h"

optionalt<mp_integer> member_offset(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  mp_integer result = 0;
  std::size_t bit_field_bits = 0;

  for(const auto &comp : type.components())
  {
    if(comp.get_name() == member)
      return result;

    if(comp.type().id() == ID_c_bit_field)
    {
      const std::size_t w = to_c_bit_field_type(comp.type()).get_width();
      bit_field_bits += w;
      result += bit_field_bits / 8;
      bit_field_bits %= 8;
    }
    else if(comp.type().id() == ID_bool)
    {
      ++bit_field_bits;
      result += bit_field_bits / 8;
      bit_field_bits %= 8;
    }
    else
    {
      DATA_INVARIANT(
        bit_field_bits == 0, "padding ensures offset at byte boundaries");
      const auto sub_size = pointer_offset_size(comp.type(), ns);
      if(!sub_size.has_value())
        return {};
      else
        result += *sub_size;
    }
  }

  return result;
}

optionalt<mp_integer> member_offset_bits(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  mp_integer offset=0;
  const struct_typet::componentst &components=type.components();

  for(const auto &comp : components)
  {
    if(comp.get_name()==member)
      return offset;

    auto member_bits = pointer_offset_bits(comp.type(), ns);
    if(!member_bits.has_value())
      return {};

    offset += *member_bits;
  }

  return {};
}

/// Compute the size of a type in bytes, rounding up to full bytes
optionalt<mp_integer>
pointer_offset_size(const typet &type, const namespacet &ns)
{
  auto bits = pointer_offset_bits(type, ns);

  if(bits.has_value())
    return (*bits + 7) / 8;
  else
    return {};
}

optionalt<mp_integer>
pointer_offset_bits(const typet &type, const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    auto sub = pointer_offset_bits(to_array_type(type).subtype(), ns);
    if(!sub.has_value())
      return {};

    // get size - we can only distinguish the elements if the size is constant
    const auto size = numeric_cast<mp_integer>(to_array_type(type).size());
    if(!size.has_value())
      return {};

    return (*sub) * (*size);
  }
  else if(type.id()==ID_vector)
  {
    auto sub = pointer_offset_bits(to_vector_type(type).subtype(), ns);
    if(!sub.has_value())
      return {};

    // get size
    const mp_integer size =
      numeric_cast_v<mp_integer>(to_vector_type(type).size());

    return (*sub) * size;
  }
  else if(type.id()==ID_complex)
  {
    auto sub = pointer_offset_bits(to_complex_type(type).subtype(), ns);

    if(sub.has_value())
      return (*sub) * 2;
    else
      return {};
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    mp_integer result=0;

    for(const auto &c : struct_type.components())
    {
      const typet &subtype = c.type();
      auto sub_size = pointer_offset_bits(subtype, ns);

      if(!sub_size.has_value())
        return {};

      result += *sub_size;
    }

    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);
    mp_integer result=0;

    // compute max

    for(const auto &c : union_type.components())
    {
      const typet &subtype = c.type();
      auto sub_size = pointer_offset_bits(subtype, ns);

      if(!sub_size.has_value())
        return {};

      if(*sub_size > result)
        result = *sub_size;
    }

    return result;
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_bool ||
          type.id()==ID_c_bit_field)
  {
    return mp_integer(to_bitvector_type(type).get_width());
  }
  else if(type.id()==ID_c_enum)
  {
    return mp_integer(to_bitvector_type(to_c_enum_type(type).subtype()).get_width());
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return pointer_offset_bits(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }
  else if(type.id()==ID_bool)
  {
    return mp_integer(1);
  }
  else if(type.id()==ID_pointer)
  {
    // the following is an MS extension
    if(type.get_bool(ID_C_ptr32))
      return mp_integer(32);

    return mp_integer(to_bitvector_type(type).get_width());
  }
  else if(type.id() == ID_symbol_type)
  {
    return pointer_offset_bits(ns.follow(type), ns);
  }
  else if(type.id() == ID_union_tag)
  {
    return pointer_offset_bits(ns.follow_tag(to_union_tag_type(type)), ns);
  }
  else if(type.id() == ID_struct_tag)
  {
    return pointer_offset_bits(ns.follow_tag(to_struct_tag_type(type)), ns);
  }
  else if(type.id()==ID_code)
  {
    return mp_integer(0);
  }
  else if(type.id()==ID_string)
  {
    return mp_integer(32);
  }
  else
    return {};
}

exprt member_offset_expr(
  const member_exprt &member_expr,
  const namespacet &ns)
{
  // need to distinguish structs and unions
  const typet &type=ns.follow(member_expr.struct_op().type());
  if(type.id()==ID_struct)
    return member_offset_expr(
      to_struct_type(type), member_expr.get_component_name(), ns);
  else if(type.id()==ID_union)
    return from_integer(0, size_type());
  else
    return nil_exprt();
}

exprt member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  exprt result=from_integer(0, size_type());
  std::size_t bit_field_bits=0;

  for(const auto &c : type.components())
  {
    if(c.get_name() == member)
      break;

    if(c.type().id() == ID_c_bit_field)
    {
      std::size_t w = to_c_bit_field_type(c.type()).get_width();
      bit_field_bits += w;
      const std::size_t bytes = bit_field_bits / 8;
      bit_field_bits %= 8;
      if(bytes > 0)
        result = plus_exprt(result, from_integer(bytes, result.type()));
    }
    else if(c.type().id() == ID_bool)
    {
      ++bit_field_bits;
      const std::size_t bytes = bit_field_bits / 8;
      bit_field_bits %= 8;
      if(bytes > 0)
        result = plus_exprt(result, from_integer(bytes, result.type()));
    }
    else
    {
      DATA_INVARIANT(
        bit_field_bits == 0, "padding ensures offset at byte boundaries");
      const typet &subtype = c.type();
      exprt sub_size=size_of_expr(subtype, ns);
      if(sub_size.is_nil())
        return nil_exprt(); // give up
      result=plus_exprt(result, sub_size);
    }
  }

  simplify(result, ns);

  return result;
}

exprt size_of_expr(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    const auto &array_type = to_array_type(type);

    // special-case arrays of bits
    if(array_type.subtype().id() == ID_bool)
    {
      auto bits = pointer_offset_bits(array_type, ns);

      if(bits.has_value())
        return from_integer((*bits + 7) / 8, size_type());
    }

    exprt sub = size_of_expr(array_type.subtype(), ns);
    if(sub.is_nil())
      return nil_exprt();

    // get size
    exprt size = array_type.size();

    if(size.is_nil())
      return nil_exprt();

    if(size.type()!=sub.type())
      size.make_typecast(sub.type());

    mult_exprt result(size, sub);
    simplify(result, ns);

    return std::move(result);
  }
  else if(type.id()==ID_vector)
  {
    const auto &vector_type = to_vector_type(type);

    // special-case vectors of bits
    if(vector_type.subtype().id() == ID_bool)
    {
      auto bits = pointer_offset_bits(vector_type, ns);

      if(bits.has_value())
        return from_integer((*bits + 7) / 8, size_type());
    }

    exprt sub = size_of_expr(vector_type.subtype(), ns);
    if(sub.is_nil())
      return nil_exprt();

    // get size
    exprt size=to_vector_type(type).size();

    if(size.is_nil())
      return nil_exprt();

    if(size.type()!=sub.type())
      size.make_typecast(sub.type());

    mult_exprt result(size, sub);
    simplify(result, ns);

    return std::move(result);
  }
  else if(type.id()==ID_complex)
  {
    exprt sub = size_of_expr(to_complex_type(type).subtype(), ns);
    if(sub.is_nil())
      return nil_exprt();

    const exprt size=from_integer(2, sub.type());

    mult_exprt result(size, sub);
    simplify(result, ns);

    return std::move(result);
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);

    exprt result=from_integer(0, size_type());
    std::size_t bit_field_bits=0;

    for(const auto &c : struct_type.components())
    {
      if(c.type().id() == ID_c_bit_field)
      {
        std::size_t w = to_c_bit_field_type(c.type()).get_width();
        bit_field_bits += w;
        const std::size_t bytes = bit_field_bits / 8;
        bit_field_bits %= 8;
        if(bytes > 0)
          result = plus_exprt(result, from_integer(bytes, result.type()));
      }
      else if(c.type().id() == ID_bool)
      {
        ++bit_field_bits;
        const std::size_t bytes = bit_field_bits / 8;
        bit_field_bits %= 8;
        if(bytes > 0)
          result = plus_exprt(result, from_integer(bytes, result.type()));
      }
      else
      {
        DATA_INVARIANT(
          bit_field_bits == 0, "padding ensures offset at byte boundaries");
        const typet &subtype = c.type();
        exprt sub_size=size_of_expr(subtype, ns);
        if(sub_size.is_nil())
          return nil_exprt();

        result=plus_exprt(result, sub_size);
      }
    }

    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_union)
  {
    const union_typet &union_type=to_union_type(type);

    mp_integer max_bytes=0;
    exprt result=from_integer(0, size_type());

    // compute max

    for(const auto &c : union_type.components())
    {
      const typet &subtype = c.type();
      exprt sub_size;

      auto sub_bits = pointer_offset_bits(subtype, ns);

      if(!sub_bits.has_value())
      {
        max_bytes=-1;

        sub_size=size_of_expr(subtype, ns);
        if(sub_size.is_nil())
          return nil_exprt();
      }
      else
      {
        mp_integer sub_bytes = (*sub_bits + 7) / 8;

        if(max_bytes>=0)
        {
          if(max_bytes<sub_bytes)
          {
            max_bytes=sub_bytes;
            result=from_integer(sub_bytes, size_type());
          }

          continue;
        }

        sub_size=from_integer(sub_bytes, size_type());
      }

      result=if_exprt(
        binary_relation_exprt(result, ID_lt, sub_size),
        sub_size, result);

      simplify(result, ns);
    }

    return result;
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_bool ||
          type.id()==ID_c_bit_field)
  {
    std::size_t width=to_bitvector_type(type).get_width();
    std::size_t bytes=width/8;
    if(bytes*8!=width)
      bytes++;
    return from_integer(bytes, size_type());
  }
  else if(type.id()==ID_c_enum)
  {
    std::size_t width =
      to_bitvector_type(to_c_enum_type(type).subtype()).get_width();
    std::size_t bytes=width/8;
    if(bytes*8!=width)
      bytes++;
    return from_integer(bytes, size_type());
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return size_of_expr(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }
  else if(type.id()==ID_bool)
  {
    return from_integer(1, size_type());
  }
  else if(type.id()==ID_pointer)
  {
    // the following is an MS extension
    if(type.get_bool(ID_C_ptr32))
      return from_integer(4, size_type());

    std::size_t width=to_bitvector_type(type).get_width();
    std::size_t bytes=width/8;
    if(bytes*8!=width)
      bytes++;
    return from_integer(bytes, size_type());
  }
  else if(type.id() == ID_symbol_type)
  {
    return size_of_expr(ns.follow(type), ns);
  }
  else if(type.id() == ID_union_tag)
  {
    return size_of_expr(ns.follow_tag(to_union_tag_type(type)), ns);
  }
  else if(type.id() == ID_struct_tag)
  {
    return size_of_expr(ns.follow_tag(to_struct_tag_type(type)), ns);
  }
  else if(type.id()==ID_code)
  {
    return from_integer(0, size_type());
  }
  else if(type.id()==ID_string)
  {
    return from_integer(32/8, size_type());
  }
  else
    return nil_exprt();
}

optionalt<mp_integer>
compute_pointer_offset(const exprt &expr, const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    if(is_ssa_expr(expr))
      return compute_pointer_offset(
        to_ssa_expr(expr).get_original_expr(), ns);
    else
      return mp_integer(0);
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    DATA_INVARIANT(
      index_expr.array().type().id() == ID_array,
      "index into array expected, found " +
        index_expr.array().type().id_string());

    auto o = compute_pointer_offset(index_expr.array(), ns);

    if(o.has_value())
    {
      const auto &array_type = to_array_type(index_expr.array().type());
      auto sub_size = pointer_offset_size(array_type.subtype(), ns);

      if(sub_size.has_value() && *sub_size > 0)
      {
        const auto i = numeric_cast<mp_integer>(index_expr.index());
        if(i.has_value())
          return (*o) + (*i) * (*sub_size);
      }
    }

    // don't know
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    const exprt &op=member_expr.struct_op();
    const struct_union_typet &type=to_struct_union_type(ns.follow(op.type()));

    auto o = compute_pointer_offset(op, ns);

    if(o.has_value())
    {
      if(type.id()==ID_union)
        return *o;

      auto member_offset = ::member_offset(
        to_struct_type(type), member_expr.get_component_name(), ns);

      if(member_offset.has_value())
        return *o + *member_offset;
    }
  }
  else if(expr.id()==ID_string_constant)
    return mp_integer(0);

  return {}; // don't know
}

exprt build_sizeof_expr(
  const constant_exprt &expr,
  const namespacet &ns)
{
  const typet &type=
    static_cast<const typet &>(expr.find(ID_C_c_sizeof_type));

  if(type.is_nil())
    return nil_exprt();

  const auto type_size = pointer_offset_size(type, ns);
  auto val = numeric_cast<mp_integer>(expr);

  if(
    !type_size.has_value() || *type_size < 0 || !val.has_value() ||
    *val < *type_size || (*type_size == 0 && *val > 0))
  {
    return nil_exprt();
  }

  const typet t(size_type());
  DATA_INVARIANT(
    address_bits(*val + 1) <= *pointer_offset_bits(t, ns),
    "sizeof value does not fit size_type");

  mp_integer remainder=0;

  if(*type_size != 0)
  {
    remainder = *val % *type_size;
    *val -= remainder;
    *val /= *type_size;
  }

  exprt result(ID_sizeof, t);
  result.set(ID_type_arg, type);

  if(*val > 1)
    result = mult_exprt(result, from_integer(*val, t));
  if(remainder>0)
    result=plus_exprt(result, from_integer(remainder, t));

  if(result.type()!=expr.type())
    result.make_typecast(expr.type());

  return result;
}

exprt get_subexpression_at_offset(
  const exprt &expr,
  const mp_integer &offset_bytes,
  const typet &target_type_raw,
  const namespacet &ns)
{
  if(offset_bytes == 0 && base_type_eq(expr.type(), target_type_raw, ns))
  {
    exprt result = expr;

    if(expr.type() != target_type_raw)
      result.type() = target_type_raw;

    return result;
  }

  const typet &source_type = ns.follow(expr.type());
  const auto target_size_bits = pointer_offset_bits(target_type_raw, ns);
  if(!target_size_bits.has_value())
    return nil_exprt();

  if(source_type.id()==ID_struct)
  {
    const struct_typet &struct_type = to_struct_type(source_type);

    mp_integer m_offset_bits = 0;
    for(const auto &component : struct_type.components())
    {
      const auto m_size_bits = pointer_offset_bits(component.type(), ns);
      if(!m_size_bits.has_value())
        return nil_exprt();

      // if this member completely contains the target, and this member is
      // byte-aligned, recurse into it
      if(
        offset_bytes * 8 >= m_offset_bits && m_offset_bits % 8 == 0 &&
        offset_bytes * 8 + *target_size_bits <= m_offset_bits + *m_size_bits)
      {
        const member_exprt member(expr, component.get_name(), component.type());
        return get_subexpression_at_offset(
          member, offset_bytes - m_offset_bits / 8, target_type_raw, ns);
      }

      m_offset_bits += *m_size_bits;
    }
  }
  else if(source_type.id()==ID_array)
  {
    const array_typet &array_type = to_array_type(source_type);

    const auto elem_size_bits = pointer_offset_bits(array_type.subtype(), ns);

    // no arrays of non-byte-aligned, zero-, or unknown-sized objects
    if(
      !elem_size_bits.has_value() || *elem_size_bits == 0 ||
      *elem_size_bits % 8 != 0)
    {
      return nil_exprt();
    }

    if(*target_size_bits <= *elem_size_bits)
    {
      const mp_integer elem_size_bytes = *elem_size_bits / 8;
      return get_subexpression_at_offset(
        index_exprt(
          expr, from_integer(offset_bytes / elem_size_bytes, index_type())),
        offset_bytes % elem_size_bytes,
        target_type_raw,
        ns);
    }
  }

  return byte_extract_exprt(
    byte_extract_id(),
    expr,
    from_integer(offset_bytes, index_type()),
    target_type_raw);
}

exprt get_subexpression_at_offset(
  const exprt &expr,
  const exprt &offset,
  const typet &target_type,
  const namespacet &ns)
{
  const auto offset_bytes = numeric_cast<mp_integer>(offset);

  if(!offset_bytes.has_value())
    return nil_exprt();
  else
    return get_subexpression_at_offset(expr, *offset_bytes, target_type, ns);
}
