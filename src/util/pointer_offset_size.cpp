/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Logic

#include "pointer_offset_size.h"

#include "arith_tools.h"
#include "c_types.h"
#include "invariant.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "ssa_expr.h"
#include "std_expr.h"

member_offset_iterator::member_offset_iterator(
  const struct_typet &_type,
  const namespacet &_ns):
  current({0, 0}),
  type(_type),
  ns(_ns),
  bit_field_bits(0)
{
}

member_offset_iterator &member_offset_iterator::operator++()
{
  if(current.second!=-1) // Already failed?
  {
    const auto &comp=type.components()[current.first];
    if(comp.type().id()==ID_c_bit_field)
    {
      // take the extra bytes needed
      std::size_t w=to_c_bit_field_type(comp.type()).get_width();
      bit_field_bits += w;
      current.second += bit_field_bits / 8;
      bit_field_bits %= 8;
    }
    else
    {
      DATA_INVARIANT(
        bit_field_bits == 0, "padding ensures offset at byte boundaries");
      const typet &subtype=comp.type();
      mp_integer sub_size=pointer_offset_size(subtype, ns);
      if(sub_size==-1)
        current.second=-1; // give up
      else current.second+=sub_size;
    }
  }
  ++current.first;
  return *this;
}

mp_integer member_offset(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  const struct_typet::componentst &components=type.components();
  member_offset_iterator offsets(type, ns);

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end() && offsets->second!=-1;
      ++it, ++offsets)
  {
    if(it->get_name()==member)
      break;
  }

  return offsets->second;
}

mp_integer member_offset_bits(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns)
{
  mp_integer offset=0;
  const struct_typet::componentst &components=type.components();

  for(const auto &comp : components)
  {
    if(comp.get_name()==member)
      break;

    mp_integer member_bits=pointer_offset_bits(comp.type(), ns);
    if(member_bits==-1)
      return member_bits;

    offset+=member_bits;
  }

  return offset;
}

/// Compute the size of a type in bytes, rounding up to full bytes
mp_integer pointer_offset_size(
  const typet &type,
  const namespacet &ns)
{
  mp_integer bits=pointer_offset_bits(type, ns);
  if(bits==-1)
    return -1;
  return (bits+7)/8;
}

mp_integer pointer_offset_bits(
  const typet &type,
  const namespacet &ns)
{
  if(type.id()==ID_array)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);
    if(sub<0)
      return -1;

    // get size
    const exprt &size=to_array_type(type).size();

    // constant?
    mp_integer i;

    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements

    return sub*i;
  }
  else if(type.id()==ID_vector)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);
    if(sub<0)
      return -1;

    // get size
    const exprt &size=to_vector_type(type).size();

    // constant?
    mp_integer i;

    if(to_integer(size, i))
      return -1; // we cannot distinguish the elements

    return sub*i;
  }
  else if(type.id()==ID_complex)
  {
    mp_integer sub=pointer_offset_bits(type.subtype(), ns);
    if(sub<0)
      return -1;

    return sub*2;
  }
  else if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);
    mp_integer result=0;

    for(const auto &c : struct_type.components())
    {
      const typet &subtype = c.type();
      mp_integer sub_size=pointer_offset_bits(subtype, ns);
      if(sub_size==-1)
        return -1;
      result+=sub_size;
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
      mp_integer sub_size=pointer_offset_bits(subtype, ns);
      if(sub_size==-1)
        return -1;
      if(sub_size>result)
        result=sub_size;
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
    return to_bitvector_type(type).get_width();
  }
  else if(type.id()==ID_c_enum)
  {
    return to_bitvector_type(type.subtype()).get_width();
  }
  else if(type.id()==ID_c_enum_tag)
  {
    return pointer_offset_bits(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }
  else if(type.id()==ID_bool)
  {
    return 1;
  }
  else if(type.id()==ID_pointer)
  {
    // the following is an MS extension
    if(type.get_bool(ID_C_ptr32))
      return 32;

    return to_bitvector_type(type).get_width();
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
    return 0;
  }
  else if(type.id()==ID_string)
  {
    return 32;
  }
  else
    return -1;
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
      result=plus_exprt(result, from_integer(bytes, result.type()));
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
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil())
      return nil_exprt();

    // get size
    exprt size=to_array_type(type).size();

    if(size.is_nil())
      return nil_exprt();

    if(size.type()!=sub.type())
      size.make_typecast(sub.type());

    mult_exprt result(size, sub);
    simplify(result, ns);

    return result;
  }
  else if(type.id()==ID_vector)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
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

    return result;
  }
  else if(type.id()==ID_complex)
  {
    exprt sub=size_of_expr(type.subtype(), ns);
    if(sub.is_nil())
      return nil_exprt();

    const exprt size=from_integer(2, sub.type());

    mult_exprt result(size, sub);
    simplify(result, ns);

    return result;
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
        result=plus_exprt(result, from_integer(bytes, result.type()));
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

      mp_integer sub_bits=pointer_offset_bits(subtype, ns);

      if(sub_bits==-1)
      {
        max_bytes=-1;

        sub_size=size_of_expr(subtype, ns);
        if(sub_size.is_nil())
          return nil_exprt();
      }
      else
      {
        mp_integer sub_bytes=(sub_bits+7)/8;

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
    std::size_t width=to_bitvector_type(type.subtype()).get_width();
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

mp_integer compute_pointer_offset(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol)
  {
    if(is_ssa_expr(expr))
      return compute_pointer_offset(
        to_ssa_expr(expr).get_original_expr(), ns);
    else
      return 0;
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const typet &array_type=ns.follow(index_expr.array().type());
    DATA_INVARIANT(
      array_type.id()==ID_array,
      "index into array expected, found "+array_type.id_string());

    mp_integer o=compute_pointer_offset(index_expr.array(), ns);

    if(o!=-1)
    {
      mp_integer sub_size=
        pointer_offset_size(array_type.subtype(), ns);

      mp_integer i;

      if(sub_size>0 && !to_integer(index_expr.index(), i))
        return o+i*sub_size;
    }

    // don't know
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(expr);
    const exprt &op=member_expr.struct_op();
    const struct_union_typet &type=to_struct_union_type(ns.follow(op.type()));

    mp_integer o=compute_pointer_offset(op, ns);

    if(o!=-1)
    {
      if(type.id()==ID_union)
        return o;

      return o+member_offset(
        to_struct_type(type), member_expr.get_component_name(), ns);
    }
  }
  else if(expr.id()==ID_string_constant)
    return 0;

  return -1; // don't know
}

exprt build_sizeof_expr(
  const constant_exprt &expr,
  const namespacet &ns)
{
  const typet &type=
    static_cast<const typet &>(expr.find(ID_C_c_sizeof_type));

  mp_integer type_size=-1, val=-1;

  if(type.is_not_nil())
    type_size=pointer_offset_size(type, ns);

  if(type_size<0 ||
     to_integer(expr, val) ||
     val<type_size ||
     (type_size==0 && val>0))
    return nil_exprt();

  const typet t(size_type());
  DATA_INVARIANT(
    address_bits(val+1)<=pointer_offset_bits(t, ns),
    "sizeof value does not fit size_type");

  mp_integer remainder=0;
  if(type_size!=0)
  {
    remainder=val%type_size;
    val-=remainder;
    val/=type_size;
  }

  exprt result(ID_sizeof, t);
  result.set(ID_type_arg, type);

  if(val>1)
    result=mult_exprt(result, from_integer(val, t));
  if(remainder>0)
    result=plus_exprt(result, from_integer(remainder, t));

  if(result.type()!=expr.type())
    result.make_typecast(expr.type());

  return result;
}

bool get_subexpression_at_offset(
  exprt &result,
  mp_integer offset,
  const typet &target_type_raw,
  const namespacet &ns)
{
  const typet &source_type=ns.follow(result.type());
  const typet &target_type=ns.follow(target_type_raw);

  if(offset==0 && source_type==target_type)
    return true;

  if(source_type.id()==ID_struct)
  {
    const auto &st=to_struct_type(source_type);
    const struct_typet::componentst &components=st.components();
    member_offset_iterator offsets(st, ns);
    while(offsets->first<components.size() &&
          offsets->second!=-1 &&
          offsets->second<=offset)
    {
      auto nextit=offsets;
      ++nextit;
      if((offsets->first+1)==components.size() || offset<nextit->second)
      {
        // This field might be, or might contain, the answer.
        result=
          member_exprt(
            result,
            components[offsets->first].get_name(),
            components[offsets->first].type());
        return
          get_subexpression_at_offset(
            result, offset-offsets->second, target_type, ns);
      }
      ++offsets;
    }
    return false;
  }
  else if(source_type.id()==ID_array)
  {
    // A cell of the array might be, or contain, the subexpression
    // we're looking for.
    const auto &at=to_array_type(source_type);
    mp_integer elem_size=pointer_offset_size(at.subtype(), ns);
    if(elem_size==-1)
      return false;
    mp_integer cellidx=offset/elem_size;
    if(cellidx < 0 || !cellidx.is_long())
      return false;
    offset=offset%elem_size;
    result=index_exprt(result, from_integer(cellidx, unsignedbv_typet(64)));
    return get_subexpression_at_offset(result, offset, target_type, ns);
  }
  else
    return false;
}

bool get_subexpression_at_offset(
  exprt &result,
  const exprt &offset,
  const typet &target_type,
  const namespacet &ns)
{
  mp_integer offset_const;
  if(to_integer(offset, offset_const))
    return false;
  return get_subexpression_at_offset(result, offset_const, target_type, ns);
}
