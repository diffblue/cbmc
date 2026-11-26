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

/// Whether the unnamed bit-fields of a struct or union contribute to its
/// alignment. The System V psABIs for AMD64 and i386 state in section 3.1.2,
/// Bit-Fields, that "Unnamed bit-fields' types do not affect the alignment of a
/// structure or union." GCC and Clang follow this rule on all targets except
/// those using the Microsoft ABI or AAPCS/AAPCS64 (Arm, other than on Apple
/// platforms).
static bool unnamed_bit_fields_affect_alignment()
{
  const irep_idt &arch = config.ansi_c.arch;
  const bool is_arm =
    arch == "arm64" || arch == "armel" || arch == "armhf" || arch == "arm";

  return config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO ||
         config.ansi_c.os == configt::ansi_ct::ost::OS_WIN ||
         (is_arm && config.ansi_c.os != configt::ansi_ct::ost::OS_MACOS);
}

/// Whether \p component contributes to the alignment of the struct or union
/// that it is a member of.
static bool contributes_to_aggregate_alignment(
  const struct_union_typet::componentt &component)
{
  // Padding members are derived from the other members, and must not
  // contribute: the padding member of a union spans the entire union, and the
  // padding following an unnamed bit-field may be wider than the alignment of
  // any member that contributes.
  if(component.get_is_padding())
    return false;

  return !component.get_anonymous() ||
         component.type().id() != ID_c_bit_field ||
         unnamed_bit_fields_affect_alignment();
}

// Forward declaration: the alignment used to lay out a component within an
// aggregate, which depends on whether the aggregate is packed.
static bytest member_layout_alignment(
  const struct_union_typet::componentt &component,
  bool container_is_packed,
  const namespacet &ns);

std::optional<bytest> layout_attribute(const irept &src, const irep_idt &id)
{
  // the cast is safe as exprt adds no data members to irept
  const exprt &value = static_cast<const exprt &>(src.find(id));
  if(value.is_nil() || value.id() == ID_default)
    return {};
  return numeric_cast<bytest>(value);
}

/// \return the maximum alignment set by a `#pragma pack(n)` in effect for
///   \p src (a component, or, with Visual Studio, an aggregate), or 0 when
///   there is none
static bytest pragma_pack(const irept &src)
{
  return layout_attribute(src, ID_C_pragma_pack).value_or(bytest{0});
}

static bool is_visual_studio()
{
  return config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO;
}

/// \return the value of the alignment attribute \p id (ID_C_alignment or
///   ID_C_declaration_alignment) of \p src, or 0 when there is none
static bytest alignment_attribute(const irept &src, const irep_idt &id)
{
  return layout_attribute(src, id).value_or(bytest{0});
}

/// \return the natural alignment of \p type, which must not be a struct,
///   union, or tag type, ignoring any explicit alignment or packing of
///   \p type itself
static bytest natural_alignment(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_array)
    return alignment(to_array_type(type).element_type(), ns);
  else if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_fixedbv || type.id() == ID_floatbv ||
    type.id() == ID_c_bool || type.id() == ID_pointer)
  {
    // Scalars are aligned to their size, or, if that is not a power of two,
    // to the largest power of two that divides the size: the 12-byte long
    // double of i386 has an alignment of 4.
    const bytest size = *pointer_offset_size(type, ns);
    bytest result{1};
    while(size > bytest{0} && size % (result * 2) == bytest{0})
      result = result * 2;
    return result;
  }
  else if(type.id() == ID_c_enum)
    return alignment(to_c_enum_type(type).underlying_type(), ns);
  else if(type.id() == ID_c_bit_field)
  {
    // we align these according to the 'underlying type'
    return alignment(to_c_bit_field_type(type).underlying_type(), ns);
  }
  else
    return bytest{1};
}

/// The alignment of \p type, ignoring any alignment that an attribute of a
/// declaration requests for the declared entity (ID_C_declaration_alignment).
static bytest type_alignment(const typet &type, const namespacet &ns)
{
  // The alignment of a type derives from:
  // - an explicit alignment of the type (ID_C_alignment), e.g., from a typedef
  //   or a struct/union definition,
  // - packing (ID_C_packed), which reduces it,
  // - or the natural alignment of the type.
  // For an aggregate the alignment is the maximum of its members' alignments
  // (computed in the aggregate's own packing context), which an explicit
  // attribute can only raise. For other types an explicit alignment is taken
  // verbatim, matching GCC/Clang where a typedef may request an alignment
  // smaller than the natural one.
  const bytest a_int = alignment_attribute(type, ID_C_alignment);

  // follow tags to the underlying definition, unless the tag type carries an
  // alignment of its own (from a typedef)
  if(
    type.id() == ID_struct_tag || type.id() == ID_union_tag ||
    type.id() == ID_c_enum_tag)
  {
    if(a_int > bytest{0})
      return a_int;
    else if(type.id() == ID_struct_tag)
      return type_alignment(ns.follow_tag(to_struct_tag_type(type)), ns);
    else if(type.id() == ID_union_tag)
      return type_alignment(ns.follow_tag(to_union_tag_type(type)), ns);
    else
      return type_alignment(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  }

  const bool packed = type.get_bool(ID_C_packed);

  // Aggregates: the alignment is the maximum of the members' layout alignments
  // (padding members do not contribute), which an explicit attribute can only
  // raise.
  if(type.id() == ID_struct || type.id() == ID_union)
  {
    bytest result{1};
    for(const auto &c : to_struct_union_type(type).components())
    {
      if(!contributes_to_aggregate_alignment(c))
        continue;
      // With Visual Studio, bit-fields do not affect the alignment of a union
      // (but its size, see add_padding).
      if(
        type.id() == ID_union && c.type().id() == ID_c_bit_field &&
        is_visual_studio())
      {
        continue;
      }
      result = std::max(result, member_layout_alignment(c, packed, ns));
    }
    return std::max(result, a_int);
  }

  // An explicit alignment of any other type is taken verbatim, matching
  // GCC/Clang where a typedef may request an alignment smaller than the
  // natural one. Visual Studio, however, does not let __declspec(align(n))
  // reduce the alignment (and warns).
  if(a_int > bytest{0})
  {
    if(is_visual_studio())
      return std::max(a_int, natural_alignment(type, ns));
    return a_int;
  }

  // no explicit alignment, but packing: dense packing, i.e. alignment 1
  if(packed)
    return bytest{1};

  return natural_alignment(type, ns);
}

/// Visual Studio does not let `#pragma pack(n)` reduce an alignment that
/// `__declspec(align(m))` requires.
/// \return the largest alignment that `__declspec(align(m))` requires for
///   \p type or any of its members, or 0 when there is none
static bytest msvc_declspec_alignment(const typet &type, const namespacet &ns)
{
  bytest result = alignment_attribute(type, ID_C_alignment);

  if(type.id() == ID_array)
  {
    return std::max(
      result, msvc_declspec_alignment(to_array_type(type).element_type(), ns));
  }
  else if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    // the tag type may carry an alignment of its own (from a typedef)
    return std::max(
      result,
      msvc_declspec_alignment(
        ns.follow_tag(to_struct_or_union_tag_type(type)), ns));
  }

  if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      result = std::max(result, msvc_declspec_alignment(c.type(), ns));
  }
  return result;
}

bytest alignment(const typet &type, const namespacet &ns)
{
  // An alignment that a declaration requests for the declared entity can only
  // increase the alignment of the entity's type.
  return std::max(
    type_alignment(type, ns),
    alignment_attribute(type, ID_C_declaration_alignment));
}

/// The alignment of \p comp_type when used as the type of a component in an
/// aggregate that is packed iff \p container_is_packed, ignoring any
/// `#pragma pack`.
static bytest member_layout_alignment_unconstrained(
  const typet &comp_type,
  bool container_is_packed,
  const namespacet &ns)
{
  // The component or the enclosing aggregate is packed (e.g.,
  // struct __attribute__((packed))): members are densely packed to a single
  // byte, irrespective of the alignment of their type. Otherwise, the
  // alignment of the type applies, which may also be smaller than the natural
  // one (e.g., with a typedef that reduces the alignment).
  const bytest base = container_is_packed || comp_type.get_bool(ID_C_packed)
                        ? bytest{1}
                        : type_alignment(comp_type, ns);

  // An alignment attribute of the member's declaration can only raise the
  // alignment, but it does so even when packed, matching GCC/Clang.
  return std::max(
    base, alignment_attribute(comp_type, ID_C_declaration_alignment));
}

/// \return the alignment that an attribute of the declaration of the bit-field
///   \p component requests for its start (capped by `#pragma pack(n)`), or 0
///   when there is none
static bytest
bit_field_start_alignment(const struct_union_typet::componentt &component)
{
  const bytest a =
    alignment_attribute(component.type(), ID_C_declaration_alignment);
  const bytest max_alignment = pragma_pack(component);
  return max_alignment > bytest{0} ? std::min(a, max_alignment) : a;
}

/// The alignment used to lay out \p component within an aggregate. This
/// implements the rules that depend on the context of the component:
/// - bit-fields are densely packed in a packed aggregate, unless a
///   `#pragma pack(n)` is in effect, which then caps their alignment at n;
///   a zero-width bit-field only affects the alignment of the aggregate with
///   the ARM ABIs (other than Apple's);
/// - the alignment of any other component is the alignment of its type in
///   the packing context of the aggregate (see
///   member_layout_alignment_unconstrained), raised by any alignment that
///   the declaration of the component requests;
/// - `#pragma pack(n)` caps the result at n, except that Visual Studio does
///   not let it reduce an alignment that `__declspec(align(m))` requires.
/// \param component: the component of the aggregate
/// \param container_is_packed: whether the aggregate is packed
/// \param ns: namespace to resolve tag types
/// \return the alignment of \p component in bytes
static bytest member_layout_alignment(
  const struct_union_typet::componentt &component,
  bool container_is_packed,
  const namespacet &ns)
{
  if(component.type().id() == ID_c_bit_field && !is_visual_studio())
  {
    const c_bit_field_typet &bit_field_type =
      to_c_bit_field_type(component.type());

    // A zero-width bit-field aligns the next member. As it is an unnamed
    // bit-field, it also affects the alignment of the aggregate only where
    // unnamed bit-fields do (see unnamed_bit_fields_affect_alignment),
    // irrespective of packing.
    if(bit_field_type.get_width() == 0)
    {
      if(unnamed_bit_fields_affect_alignment())
        return alignment(bit_field_type.underlying_type(), ns);
      return bytest{1};
    }

    // Bit-fields are densely packed in a packed aggregate -- unless
    // #pragma pack(n) is in effect, which then caps their alignment at n
    // instead, as GCC and Clang do. An alignment attribute of the bit-field's
    // declaration can only raise the alignment (subject to #pragma pack).
    const bytest natural = alignment(bit_field_type.underlying_type(), ns);
    const bytest max_alignment = pragma_pack(component);
    const bytest base =
      max_alignment > bytest{0} ? std::min(max_alignment, natural)
      : container_is_packed || bit_field_type.get_bool(ID_C_packed) ? bytest{1}
                                                                    : natural;
    return std::max(base, bit_field_start_alignment(component));
  }

  const bytest a = member_layout_alignment_unconstrained(
    component.type(), container_is_packed, ns);

  // #pragma pack(n) caps the alignment of each member at n ("a multiple of n
  // or of the member's size, whichever is smaller"), including any alignment
  // requested by an attribute on the member.
  const bytest max_alignment = pragma_pack(component);
  if(max_alignment > bytest{0})
  {
    if(is_visual_studio())
    {
      return std::max(
        std::min(max_alignment, a),
        msvc_declspec_alignment(component.type(), ns));
    }
    return std::min(max_alignment, a);
  }

  return a;
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

/// Visual Studio pads the size of an aggregate up to its alignment, but caps
/// this at the `#pragma pack(n)` in effect at the end of its definition,
/// unless `__declspec(align(m))` requires a larger alignment.
static bytest
msvc_trailing_padding_alignment(const typet &type, const namespacet &ns)
{
  const bytest a = alignment(type, ns);
  const bytest max_alignment = pragma_pack(type);
  if(max_alignment == bytest{0})
    return a;
  return std::max(
    std::min(a, max_alignment), msvc_declspec_alignment(type, ns));
}

static void add_padding_msvc(struct_typet &type, const namespacet &ns)
{
  struct_typet::componentst &components = type.components();

  std::size_t bit_field_bits = 0, underlying_bits = 0;
  bytest offset{0};

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
      // do not add padding, but count the bits -- unless the bit-field does
      // not fit into the remaining bits of the current unit, in which case
      // it starts a new unit
      const auto width = to_c_bit_field_type(it->type()).get_width();
      const std::size_t used_bits = bit_field_bits % underlying_bits;
      if(used_bits != 0 && used_bits + width > underlying_bits)
      {
        const std::size_t pad_bits = underlying_bits - used_bits;
        it = pad_bit_field(components, it, pad_bits);
        bit_field_bits += pad_bits;
      }
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
        offset += bits_to_bytes_trunc(
          bitst{bit_field_bits + pad_bits}, config.ansi_c.char_width);
        underlying_bits = bit_field_bits = 0;
      }
      else
      {
        offset +=
          bits_to_bytes_trunc(bitst{bit_field_bits}, config.ansi_c.char_width);
        underlying_bits = bit_field_bits = 0;
      }

      // pad up to underlying type unless the struct is packed
      if(!is_packed)
      {
        const bytest a = member_layout_alignment(*it, false, ns);
        if(a > bytest{1})
        {
          const bytest displacement = offset % a;

          if(displacement != bytest{0})
          {
            const bytest pad_bytes = a - displacement;
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
        if(size.has_value() && *size >= bytest{1})
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
    offset += bits_to_bytes_trunc(
      bitst{bit_field_bits + pad}, config.ansi_c.char_width);
  }
  else
  {
    offset +=
      bits_to_bytes_trunc(bitst{bit_field_bits}, config.ansi_c.char_width);
  }

  // alignment of the struct
  // Note that this is done even if the struct is packed.
  const bytest a = msvc_trailing_padding_alignment(type, ns);
  const bytest displacement = offset % a;

  if(displacement != bytest{0})
  {
    const bytest pad_bytes = a - displacement;
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
    std::size_t bit_field_bits = 0;

    for(struct_typet::componentst::iterator it = components.begin();
        it != components.end();
        it++)
    {
      if(
        it->type().id() == ID_c_bit_field &&
        to_c_bit_field_type(it->type()).get_width() != 0)
      {
        // a bit-field with an alignment attribute starts on a byte boundary
        if(
          bit_field_start_alignment(*it) > bytest{1} &&
          bit_field_bits % config.ansi_c.char_width != 0)
        {
          const std::size_t pad = config.ansi_c.char_width -
                                  bit_field_bits % config.ansi_c.char_width;
          it = pad_bit_field(components, it, pad);
          bit_field_bits = 0;
        }

        // count the bits
        const std::size_t width = to_c_bit_field_type(it->type()).get_width();
        bit_field_bits += width;
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

  bytest offset{0};
  bytest max_alignment{0};
  std::size_t bit_field_bits=0;
  const bool struct_is_packed = type.get_bool(ID_C_packed);

  for(struct_typet::componentst::iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet it_type=it->type();
    bytest a{1};
    const bytest max_alignment_pragma = pragma_pack(*it);

    if(it_type.id() == ID_c_bit_field)
    {
      if(to_c_bit_field_type(it_type).get_width() == 0)
      {
        // A zero-width bit-field causes alignment of the next member to the
        // underlying type, irrespective of packing.
        a = alignment(to_c_bit_field_type(it_type).underlying_type(), ns);
        max_alignment = std::max(
          max_alignment, member_layout_alignment(*it, struct_is_packed, ns));
        DATA_INVARIANT(
          bit_field_bits == 0, "padding ensures offset at byte boundaries");
        const bytest displacement = offset % a;
        if(displacement != bytest{0})
        {
          const bytest pad_bytes = a - displacement;
          const std::size_t pad_bits =
            numeric_cast_v<std::size_t>(pad_bytes * config.ansi_c.char_width);
          it = pad(components, it, pad_bits);
          offset += pad_bytes;
        }
        continue;
      }
      else
      {
        // Otherwise, ANSI-C says that bit-fields do not get padded!
        // We consider the type for max_alignment, however, unless this is an
        // unnamed bit-field that does not contribute.
        a = member_layout_alignment(*it, struct_is_packed, ns);
        if(contributes_to_aggregate_alignment(*it) && max_alignment < a)
          max_alignment = a;

        // Unless an alignment attribute requests to start the bit-field at an
        // aligned offset.
        const bytest start_alignment = bit_field_start_alignment(*it);
        if(start_alignment > bytest{1})
        {
          DATA_INVARIANT(
            bit_field_bits == 0, "padding ensures offset at byte boundaries");
          const bytest displacement = offset % start_alignment;
          if(displacement != bytest{0})
          {
            const bytest pad_bytes = start_alignment - displacement;
            it = pad(
              components,
              it,
              numeric_cast_v<std::size_t>(
                pad_bytes * config.ansi_c.char_width));
            offset += pad_bytes;
          }
        }

        std::size_t w = to_c_bit_field_type(it_type).get_width();
        bit_field_bits += w;
        const std::size_t bytes = bit_field_bits / config.ansi_c.char_width;
        bit_field_bits %= config.ansi_c.char_width;
        offset += bytest{bytes};
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
      offset += bytest{bytes};
      continue;
    }
    else
      a = member_layout_alignment(*it, struct_is_packed, ns);

    DATA_INVARIANT(
      bit_field_bits == 0, "padding ensures offset at byte boundaries");

    // check minimum alignment
    if(
      a < config.ansi_c.alignment && max_alignment_pragma == bytest{0} &&
      !it_type.get_bool(ID_C_packed) &&
      (it_type.id() != ID_struct_tag ||
       !ns.follow_tag(to_struct_tag_type(it_type)).get_bool(ID_C_packed)) &&
      (it_type.id() != ID_union_tag ||
       !ns.follow_tag(to_union_tag_type(it_type)).get_bool(ID_C_packed)))
    {
      a = config.ansi_c.alignment;
    }

    if(contributes_to_aggregate_alignment(*it) && max_alignment < a)
      max_alignment = a;

    if(a != bytest{1})
    {
      // we may need to align it
      const bytest displacement = offset % a;

      if(displacement != bytest{0})
      {
        const bytest pad_bytes = a - displacement;
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
      const auto tmp_i = numeric_cast<bytest>(simplify_expr(alignment, ns));

      if(tmp_i.has_value() && *tmp_i > max_alignment)
        max_alignment = *tmp_i;
    }
  }
  // Is the struct packed, without any alignment specification, and with no
  // member forcing a larger alignment? Then there is no end-of-struct padding.
  // (If a member carries an explicit alignment attribute, max_alignment is
  // greater than one and the struct is still padded up to it, as GCC/Clang do.)
  else if(struct_is_packed && max_alignment <= bytest{1})
    return; // done

  // There may be a need for 'end of struct' padding.
  // We use 'max_alignment'.

  if(max_alignment > bytest{1})
  {
    // we may need to align it
    bytest displacement = offset % max_alignment;

    if(displacement != bytest{0})
    {
      bytest pad_bytes = max_alignment - displacement;
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
  bitst max_alignment_bits = bytes_to_bits(
    is_visual_studio() ? msvc_trailing_padding_alignment(type, ns)
                       : alignment(type, ns),
    config.ansi_c.char_width);
  bitst size_bits{0};

  // check per component, and ignore those without fixed size
  for(const auto &c : type.components())
  {
    auto s = pointer_offset_bits(c.type(), ns);
    if(s.has_value())
      size_bits = std::max(size_bits, *s);
  }
  const bitst member_bits = size_bits;

  if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    // With Visual Studio, the size of a union is at least the size of the
    // underlying type of any bit-field.
    for(const auto &c : type.components())
      if(c.type().id() == ID_c_bit_field)
      {
        auto w = underlying_width(to_c_bit_field_type(c.type()), ns);
        if(w.has_value())
          size_bits = std::max(size_bits, bitst{w.value()});
      }
  }

  // The size must be a multiple of the alignment, or
  // we add a padding member to the union.
  if(size_bits % max_alignment_bits != bitst{0})
    size_bits += max_alignment_bits - (size_bits % max_alignment_bits);

  if(size_bits > member_bits)
  {
    unsignedbv_typet padding_type(numeric_cast_v<std::size_t>(size_bits));

    struct_typet::componentt component;
    component.type()=padding_type;
    component.set_name("$pad");
    component.set_is_padding(true);

    type.components().push_back(component);
  }
}
