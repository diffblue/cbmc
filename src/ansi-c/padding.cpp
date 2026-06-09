/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "padding.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

// Forward declaration: the alignment used to lay out a component within an
// aggregate, which depends on whether the aggregate is packed.
static mp_integer member_layout_alignment(
  const typet &comp_type,
  bool container_is_packed,
  const namespacet &ns);

mp_integer alignment(const typet &type, const namespacet &ns)
{
  // The alignment of a type derives from:
  // - an explicit alignment attribute in the source (ID_C_alignment),
  // - alignment induced by packing (ID_C_packed), which reduces it,
  // - or the natural alignment of the type.
  // For an aggregate the alignment is the maximum of its members' alignments
  // (computed in the aggregate's own packing context), which an explicit
  // attribute can only raise. For a non-aggregate an explicit attribute is
  // taken verbatim, matching GCC/Clang where e.g. a typedef may request an
  // alignment smaller than the natural one.

  // follow tags to the underlying definition
  if(type.id() == ID_struct_tag)
    return alignment(ns.follow_tag(to_struct_tag_type(type)), ns);
  else if(type.id() == ID_union_tag)
    return alignment(ns.follow_tag(to_union_tag_type(type)), ns);
  else if(type.id() == ID_c_enum_tag)
    return alignment(ns.follow_tag(to_c_enum_tag_type(type)), ns);

  const exprt &given_alignment =
    static_cast<const exprt &>(type.find(ID_C_alignment));

  mp_integer a_int = 0;
  if(given_alignment.is_not_nil() && given_alignment.id() != ID_default)
  {
    const auto a = numeric_cast<mp_integer>(given_alignment);
    if(a.has_value())
      a_int = *a;
  }

  const bool packed = type.get_bool(ID_C_packed);

  // Aggregates: the alignment is the maximum of the members' layout alignments
  // (padding members do not contribute), which an explicit attribute can only
  // raise.
  if(type.id() == ID_struct || type.id() == ID_union)
  {
    mp_integer result = 1;
    for(const auto &c : to_struct_union_type(type).components())
    {
      if(c.get_is_padding())
        continue;
      result = std::max(result, member_layout_alignment(c.type(), packed, ns));
    }
    if(a_int > result)
      result = a_int;
    return result;
  }

  // no explicit alignment, but packing: dense packing, i.e. alignment 1
  if(a_int == 0 && packed)
    return 1;

  // an explicit alignment on a non-aggregate is taken verbatim (it may even
  // request an alignment smaller than the natural one)
  if(a_int > 0)
    return a_int;

  // compute the natural alignment
  mp_integer result;

  if(type.id()==ID_array)
    result = alignment(to_array_type(type).element_type(), ns);
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
    result = alignment(to_c_enum_type(type).underlying_type(), ns);
  else if(type.id()==ID_c_bit_field)
  {
    // we align these according to the 'underlying type'
    result = alignment(to_c_bit_field_type(type).underlying_type(), ns);
  }
  else
    result=1;

  return result;
}

static mp_integer member_layout_alignment(
  const typet &comp_type,
  bool container_is_packed,
  const namespacet &ns)
{
  const exprt &given =
    static_cast<const exprt &>(comp_type.find(ID_C_alignment));
  mp_integer given_int = 0;
  if(given.is_not_nil() && given.id() != ID_default)
  {
    const auto a = numeric_cast<mp_integer>(given);
    if(a.has_value())
      given_int = *a;
  }

  // the natural alignment of the component, ignoring any explicit attribute
  // or packing flag (both of which we are about to interpret here)
  typet natural_type = comp_type;
  natural_type.remove(ID_C_alignment);
  natural_type.remove(ID_C_packed);
  const mp_integer natural = alignment(natural_type, ns);

  // A component-level packing attribute models #pragma pack(n): the parser
  // attaches both a packing flag and the alignment n to each member, and the
  // resulting alignment is the cap min(n, natural) ("a multiple of n or of the
  // member's size, whichever is smaller"). A bare packed component (no
  // alignment) is densely packed to a single byte.
  if(comp_type.get_bool(ID_C_packed))
  {
    if(given_int > 0)
      return std::min(given_int, natural);
    return 1;
  }

  // The enclosing aggregate is packed (e.g. struct __attribute__((packed))):
  // members are densely packed to a single byte, but an explicit aligned() on
  // the member is honoured verbatim and may raise or lower the alignment.
  if(container_is_packed)
    return given_int > 0 ? given_int : mp_integer{1};

  // Without any packing, an explicit alignment can only increase the natural
  // alignment of the component (GCC/Clang ignore a smaller request here).
  return given_int > natural ? given_int : natural;
}

static std::optional<std::size_t>
underlying_width(const c_bit_field_typet &type, const namespacet &ns)
{
  const typet &underlying_type = type.underlying_type();

  if(underlying_type.id() == ID_bool)
  {
    // This is the 'proper' bool.
    return 1;
  }
  else if(
    underlying_type.id() == ID_signedbv ||
    underlying_type.id() == ID_unsignedbv || underlying_type.id() == ID_c_bool)
  {
    return to_bitvector_type(underlying_type).get_width();
  }
  else if(underlying_type.id() == ID_c_enum_tag)
  {
    // These point to an enum, which has a sub-subtype,
    // which may be smaller or larger than int, and we thus have
    // to check.
    const auto &c_enum_type =
      ns.follow_tag(to_c_enum_tag_type(underlying_type));

    if(!c_enum_type.is_incomplete())
      return to_bitvector_type(c_enum_type.underlying_type()).get_width();
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
    else if(it->is_boolean() && underlying_bits == config.ansi_c.char_width)
    {
      ++bit_field_bits;
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
      else
      {
        offset += bit_field_bits / config.ansi_c.char_width;
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
      else if(it->is_boolean())
      {
        underlying_bits = config.ansi_c.char_width;
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
  else
    offset += bit_field_bits / config.ansi_c.char_width;

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
      else if(it->is_boolean())
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

  mp_integer offset=0;
  mp_integer max_alignment=0;
  std::size_t bit_field_bits=0;
  const bool struct_is_packed = type.get_bool(ID_C_packed);

  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet it_type=it->type();
    mp_integer a=1;

    if(it_type.id()==ID_c_bit_field)
    {
      a = alignment(to_c_bit_field_type(it_type).underlying_type(), ns);

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
      a = member_layout_alignment(it_type, struct_is_packed, ns);

    DATA_INVARIANT(
      bit_field_bits == 0, "padding ensures offset at byte boundaries");

    // check minimum alignment
    if(
      a < config.ansi_c.alignment && !it_type.get_bool(ID_C_packed) &&
      (it_type.id() != ID_struct_tag ||
       !ns.follow_tag(to_struct_tag_type(it_type)).get_bool(ID_C_packed)) &&
      (it_type.id() != ID_union_tag ||
       !ns.follow_tag(to_union_tag_type(it_type)).get_bool(ID_C_packed)))
    {
      a=config.ansi_c.alignment;
    }

    if(max_alignment<a)
      max_alignment=a;

    if(
      a != 1 &&
      (!struct_is_packed || it_type.find(ID_C_alignment).is_not_nil()))
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
  // Is the struct packed, without any alignment specification, and with no
  // member forcing a larger alignment? Then there is no end-of-struct padding.
  // (If a member carries an explicit alignment attribute, max_alignment is
  // greater than one and the struct is still padded up to it, as GCC/Clang do.)
  else if(struct_is_packed && max_alignment <= 1)
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
  // The union's size must be a multiple of its alignment. alignment() already
  // accounts for packing and for an explicit aligned() attribute (which raises
  // the alignment even when the union is packed), so the size is padded up to
  // that alignment, matching GCC and Clang.
  mp_integer max_alignment_bits =
    alignment(type, ns) * config.ansi_c.char_width;
  mp_integer size_bits = 0;

  // check per component, and ignore those without fixed size
  for(const auto &c : type.components())
  {
    auto s = pointer_offset_bits(c.type(), ns);
    if(s.has_value())
      size_bits = std::max(size_bits, *s);
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
