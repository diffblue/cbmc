/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "padding.h"

#include <algorithm>

#include <util/config.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

mp_integer alignment(const typet &type, const namespacet &ns)
{
  // we need to consider a number of different cases:
  // - alignment specified in the source, which will be recorded in
  // ID_C_alignment
  // - alignment induced by packing ("The alignment of a member will
  // be on a boundary that is either a multiple of n or a multiple of
  // the size of the member, whichever is smaller."); both
  // ID_C_alignment and ID_C_packed will be set
  // - natural alignment, when neither ID_C_alignment nor ID_C_packed
  // are set
  // - dense packing with only ID_C_packed set.

  // is the alignment given?
  const exprt &given_alignment=
    static_cast<const exprt &>(type.find(ID_C_alignment));

  mp_integer a_int = 0;

  // we trust it blindly, no matter how nonsensical
  if(given_alignment.is_not_nil())
  {
    const auto a = numeric_cast<mp_integer>(given_alignment);
    if(a.has_value())
      a_int = *a;
  }

  // alignment but no packing
  if(a_int>0 && !type.get_bool(ID_C_packed))
    return a_int;
  // no alignment, packing
  else if(a_int==0 && type.get_bool(ID_C_packed))
    return 1;

  // compute default
  mp_integer result;

  if(type.id()==ID_array)
    result=alignment(type.subtype(), ns);
  else if(type.id()==ID_struct || type.id()==ID_union)
  {
    result=1;

    // get the max
    // (should really be the smallest common denominator)
    for(const auto &c : to_struct_union_type(type).components())
      result = std::max(result, alignment(c.type(), ns));
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_c_bool ||
          type.id()==ID_pointer)
  {
    result = *pointer_offset_size(type, ns);
  }
  else if(type.id()==ID_c_enum)
    result=alignment(type.subtype(), ns);
  else if(type.id()==ID_c_enum_tag)
    result=alignment(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  else if(type.id() == ID_struct_tag)
    result = alignment(ns.follow_tag(to_struct_tag_type(type)), ns);
  else if(type.id() == ID_union_tag)
    result = alignment(ns.follow_tag(to_union_tag_type(type)), ns);
  else if(type.id()==ID_c_bit_field)
  {
    // we align these according to the 'underlying type'
    result=alignment(type.subtype(), ns);
  }
  else
    result=1;

  // if an alignment had been provided and packing was requested, take
  // the smallest alignment
  if(a_int>0 && a_int<result)
    result=a_int;

  return result;
}

static optionalt<std::size_t>
underlying_width(const c_bit_field_typet &type, const namespacet &ns)
{
  const typet &subtype = type.subtype();

  if(subtype.id() == ID_bool)
  {
    // This is the 'proper' bool.
    return 1;
  }
  else if(
    subtype.id() == ID_signedbv || subtype.id() == ID_unsignedbv ||
    subtype.id() == ID_c_bool)
  {
    return to_bitvector_type(subtype).get_width();
  }
  else if(subtype.id() == ID_c_enum_tag)
  {
    // These point to an enum, which has a sub-subtype,
    // which may be smaller or larger than int, and we thus have
    // to check.
    const typet &c_enum_type = ns.follow_tag(to_c_enum_tag_type(subtype));

    if(c_enum_type.id() == ID_c_enum)
      return c_enum_type.subtype().get_size_t(ID_width);
    else
      return {};
  }
  else
    return {};
}

static struct_typet::componentst::iterator pad_bit_field(
  struct_typet::componentst &components,
  struct_typet::componentst::iterator where,
  std::size_t pad_bits)
{
  const c_bit_field_typet padding_type(
    unsignedbv_typet(pad_bits), pad_bits);

  struct_typet::componentt component(
    "$bit_field_pad" + std::to_string(where - components.begin()),
    padding_type);

  component.set_is_padding(true);

  return std::next(components.insert(where, component));
}

static struct_typet::componentst::iterator pad(
  struct_typet::componentst &components,
  struct_typet::componentst::iterator where,
  std::size_t pad_bits)
{
  const unsignedbv_typet padding_type(pad_bits);

  struct_typet::componentt component(
    "$pad" + std::to_string(where - components.begin()),
    padding_type);

  component.set_is_padding(true);

  return std::next(components.insert(where, component));
}

static void add_padding_msvc(struct_typet &type, const namespacet &ns)
{
  struct_typet::componentst &components=type.components();

  std::size_t bit_field_bits = 0, underlying_bits = 0;
  mp_integer offset = 0;

  bool is_packed = type.get_bool(ID_C_packed);

  for(struct_typet::componentst::iterator it = components.begin();
      it != components.end();
      it++)
  {
    // there is exactly one case in which padding is not added:
    // if we continue a bit-field with size>0 and the same underlying width

    if(
      it->type().id() == ID_c_bit_field &&
      to_c_bit_field_type(it->type()).get_width() != 0 &&
      underlying_width(to_c_bit_field_type(it->type()), ns).value_or(0) ==
        underlying_bits)
    {
      // do not add padding, but count the bits
      const auto width = to_c_bit_field_type(it->type()).get_width();
      bit_field_bits += width;
    }
    else
    {
      // pad up any remaining bit field
      if(underlying_bits != 0 && (bit_field_bits % underlying_bits) != 0)
      {
        const std::size_t pad_bits =
          underlying_bits - (bit_field_bits % underlying_bits);
        it = pad_bit_field(components, it, pad_bits);
        offset += (bit_field_bits + pad_bits) / config.ansi_c.char_width;
        underlying_bits = bit_field_bits = 0;
      }

      // pad up to underlying type unless the struct is packed
      if(!is_packed)
      {
        const mp_integer a = alignment(it->type(), ns);
        if(a > 1)
        {
          const mp_integer displacement = offset % a;

          if(displacement != 0)
          {
            const mp_integer pad_bytes = a - displacement;
            std::size_t pad_bits =
              numeric_cast_v<std::size_t>(pad_bytes * config.ansi_c.char_width);
            it = pad(components, it, pad_bits);
            offset += pad_bytes;
          }
        }
      }

      // do we start a new bit field?
      if(it->type().id() == ID_c_bit_field)
      {
        underlying_bits =
          underlying_width(to_c_bit_field_type(it->type()), ns).value_or(0);
        const auto width = to_c_bit_field_type(it->type()).get_width();
        bit_field_bits += width;
      }
      else if(it->type().id() == ID_bool)
      {
        ++bit_field_bits;
      }
      else
      {
        // keep track of offset
        const auto size = pointer_offset_size(it->type(), ns);
        if(size.has_value() && *size >= 1)
          offset += *size;
      }
    }
  }

  // Add padding at the end?
  // Bit-field
  if(underlying_bits != 0 && (bit_field_bits % underlying_bits) != 0)
  {
    const std::size_t pad =
      underlying_bits - (bit_field_bits % underlying_bits);
    pad_bit_field(components, components.end(), pad);
    offset += (bit_field_bits + pad) / config.ansi_c.char_width;
  }

  // alignment of the struct
  // Note that this is done even if the struct is packed.
  const mp_integer a = alignment(type, ns);
  const mp_integer displacement = offset % a;

  if(displacement != 0)
  {
    const mp_integer pad_bytes = a - displacement;
    const std::size_t pad_bits =
      numeric_cast_v<std::size_t>(pad_bytes * config.ansi_c.char_width);
    pad(components, components.end(), pad_bits);
    offset += pad_bytes;
  }
}

static void add_padding_gcc(struct_typet &type, const namespacet &ns)
{
  struct_typet::componentst &components = type.components();

  // First make bit-fields appear on byte boundaries
  {
    std::size_t bit_field_bits=0;

    for(struct_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(it->type().id()==ID_c_bit_field &&
         to_c_bit_field_type(it->type()).get_width()!=0)
      {
        // count the bits
        const std::size_t width = to_c_bit_field_type(it->type()).get_width();
        bit_field_bits+=width;
      }
      else if(it->type().id() == ID_bool)
      {
        ++bit_field_bits;
      }
      else if(bit_field_bits!=0)
      {
        // not on a byte-boundary?
        if((bit_field_bits % config.ansi_c.char_width) != 0)
        {
          const std::size_t pad = config.ansi_c.char_width -
                                  bit_field_bits % config.ansi_c.char_width;
          it = pad_bit_field(components, it, pad);
        }

        bit_field_bits=0;
      }
    }

    // Add padding at the end?
    if((bit_field_bits % config.ansi_c.char_width) != 0)
    {
      const std::size_t pad =
        config.ansi_c.char_width - bit_field_bits % config.ansi_c.char_width;
      pad_bit_field(components, components.end(), pad);
    }
  }

  // Is the struct packed, without any alignment specification?
  if(type.get_bool(ID_C_packed) &&
     type.find(ID_C_alignment).is_nil())
    return; // done

  mp_integer offset=0;
  mp_integer max_alignment=0;
  std::size_t bit_field_bits=0;

  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet it_type=it->type();
    mp_integer a=1;

    const bool packed=it_type.get_bool(ID_C_packed) ||
                      ns.follow(it_type).get_bool(ID_C_packed);

    if(it_type.id()==ID_c_bit_field)
    {
      a=alignment(to_c_bit_field_type(it_type).subtype(), ns);

      // A zero-width bit-field causes alignment to the base-type.
      if(to_c_bit_field_type(it_type).get_width()==0)
      {
      }
      else
      {
        // Otherwise, ANSI-C says that bit-fields do not get padded!
        // We consider the type for max_alignment, however.
        if(max_alignment<a)
          max_alignment=a;

        std::size_t w=to_c_bit_field_type(it_type).get_width();
        bit_field_bits += w;
        const std::size_t bytes = bit_field_bits / config.ansi_c.char_width;
        bit_field_bits %= config.ansi_c.char_width;
        offset+=bytes;
        continue;
      }
    }
    else if(it_type.id() == ID_bool)
    {
      a = alignment(it_type, ns);
      if(max_alignment < a)
        max_alignment = a;

      ++bit_field_bits;
      const std::size_t bytes = bit_field_bits / config.ansi_c.char_width;
      bit_field_bits %= config.ansi_c.char_width;
      offset += bytes;
      continue;
    }
    else
      a=alignment(it_type, ns);

    DATA_INVARIANT(
      bit_field_bits == 0, "padding ensures offset at byte boundaries");

    // check minimum alignment
    if(a<config.ansi_c.alignment && !packed)
      a=config.ansi_c.alignment;

    if(max_alignment<a)
      max_alignment=a;

    if(a!=1)
    {
      // we may need to align it
      const mp_integer displacement = offset % a;

      if(displacement!=0)
      {
        const mp_integer pad_bytes = a - displacement;
        const std::size_t pad_bits =
          numeric_cast_v<std::size_t>(pad_bytes * config.ansi_c.char_width);
        it = pad(components, it, pad_bits);
        offset += pad_bytes;
      }
    }

    auto size = pointer_offset_size(it_type, ns);

    if(size.has_value())
      offset += *size;
  }

  // any explicit alignment for the struct?
  const exprt &alignment =
    static_cast<const exprt &>(type.find(ID_C_alignment));
  if(alignment.is_not_nil())
  {
    if(alignment.id()!=ID_default)
    {
      const auto tmp_i = numeric_cast<mp_integer>(simplify_expr(alignment, ns));

      if(tmp_i.has_value() && *tmp_i > max_alignment)
        max_alignment = *tmp_i;
    }
  }
  // Is the struct packed, without any alignment specification?
  else if(type.get_bool(ID_C_packed))
    return; // done

  // There may be a need for 'end of struct' padding.
  // We use 'max_alignment'.

  if(max_alignment>1)
  {
    // we may need to align it
    mp_integer displacement=offset%max_alignment;

    if(displacement!=0)
    {
      mp_integer pad_bytes = max_alignment - displacement;
      std::size_t pad_bits =
        numeric_cast_v<std::size_t>(pad_bytes * config.ansi_c.char_width);
      pad(components, components.end(), pad_bits);
    }
  }
}

void add_padding(struct_typet &type, const namespacet &ns)
{
  // padding depends greatly on compiler
  if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
    add_padding_msvc(type, ns);
  else
    add_padding_gcc(type, ns);
}

void add_padding(union_typet &type, const namespacet &ns)
{
  mp_integer max_alignment_bits =
    alignment(type, ns) * config.ansi_c.char_width;
  mp_integer size_bits=0;

  // check per component, and ignore those without fixed size
  for(const auto &c : type.components())
  {
    auto s = pointer_offset_bits(c.type(), ns);
    if(s.has_value())
      size_bits = std::max(size_bits, *s);
  }

  // Is the union packed?
  if(type.get_bool(ID_C_packed))
  {
    // The size needs to be a multiple of 1 char only.
    max_alignment_bits = config.ansi_c.char_width;
  }

  if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    // Visual Studio pads up to the underlying width of
    // any bit field.
    for(const auto &c : type.components())
      if(c.type().id() == ID_c_bit_field)
      {
        auto w = underlying_width(to_c_bit_field_type(c.type()), ns);
        if(w.has_value() && w.value() > max_alignment_bits)
          max_alignment_bits = w.value();
      }
  }

  // The size must be a multiple of the alignment, or
  // we add a padding member to the union.

  if(size_bits%max_alignment_bits!=0)
  {
    mp_integer padding_bits=
      max_alignment_bits-(size_bits%max_alignment_bits);

    unsignedbv_typet padding_type(
      numeric_cast_v<std::size_t>(size_bits + padding_bits));

    struct_typet::componentt component;
    component.type()=padding_type;
    component.set_name("$pad");
    component.set_is_padding(true);

    type.components().push_back(component);
  }
}
