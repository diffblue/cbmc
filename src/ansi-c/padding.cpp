/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "padding.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include <algorithm>
#include <map>
#include <optional>
#include <set>

// Recursion guard for `alignment`.  The public entry wraps a call
// to `alignment_rec` with an initially empty set; `alignment_rec`
// inserts the identifier of every ID_struct_tag / ID_union_tag /
// ID_c_enum_tag it dereferences and refuses to recurse into a tag
// it is already in the process of resolving.
//
// Why this matters: if the C/C++ front-end produces an ill-formed
// type graph in which a struct appears to contain itself by value
// (for example, after a failed template substitution leaves a
// partially-resolved type behind), the naive recursion in
// `alignment` blows the stack.  Hit during dog-fooding goto-cc on
// `src/util/ref_expr_set.cpp` and `src/util/output_file.cpp`: a
// front-end error cascade left `struct basic_string` with a
// self-referential component, and `alignment` recursed until
// SIGSEGV.  Per [basic.type]/1 a type is either complete or
// incomplete; an incomplete type has no alignment, so returning 1
// (the minimum alignment) for a cyclic tag is a safe
// approximation.
/// The alignment a member of a packed struct/union keeps: its own
/// `aligned(n)' attribute.  An alignment that belongs to the member's TYPE
/// (a typedef's `aligned', marked ID_C_typedef_alignment) is ignored there,
/// as GCC ignores the alignment of an aligned class type in a packed struct
/// (also when that type is defined in place, ID_C_type_alignment).  A
/// `#pragma pack(n)' cap in force for the member still applies.
static std::optional<mp_integer> explicit_member_alignment(const typet &_type)
{
  // an alignment specifier on an array member sits on the element type
  const typet *type = &_type;
  while(type->id() == ID_array && type->find(ID_C_alignment).is_nil())
    type = &to_array_type(*type).element_type();
  const exprt &given = static_cast<const exprt &>(type->find(ID_C_alignment));
  if(
    given.is_nil() || given.get_bool(ID_C_typedef_alignment) ||
    given.get_bool(ID_C_type_alignment))
    return {};
  auto result = numeric_cast<mp_integer>(given);
  const auto cap = numeric_cast<mp_integer>(
    static_cast<const exprt &>(type->find(ID_C_pragma_pack)));
  if(result.has_value() && cap.has_value() && *cap < *result)
    result = cap;
  return result;
}

/// GCC `#pragma pack(n)': "The alignment of a member will be on a boundary
/// that is either a multiple of n or a multiple of the size of the member,
/// whichever is smaller" -- the cap applies after the member's own
/// `aligned(k)' (which can only increase the natural alignment):
/// min(n, max(natural, k)).
static mp_integer apply_pragma_pack(const typet &type, mp_integer alignment)
{
  const auto cap = numeric_cast<mp_integer>(
    static_cast<const exprt &>(type.find(ID_C_pragma_pack)));
  if(cap.has_value() && *cap > 0 && *cap < alignment)
    return *cap;
  return alignment;
}

static mp_integer alignment_rec(
  const typet &type,
  const namespacet &ns,
  std::set<irep_idt> &in_progress,
  std::map<irep_idt, mp_integer> &done);

mp_integer alignment(const typet &type, const namespacet &ns)
{
  std::set<irep_idt> in_progress;
  std::map<irep_idt, mp_integer> done;
  return alignment_rec(type, ns, in_progress, done);
}

static mp_integer alignment_rec(
  const typet &type,
  const namespacet &ns,
  std::set<irep_idt> &in_progress,
  std::map<irep_idt, mp_integer> &done)
{
  // we need to consider a number of different cases:
  // - alignment specified in the source, which will be recorded in
  // ID_C_alignment
  // - alignment specified together with packing (`packed, aligned(n)');
  // both ID_C_alignment and ID_C_packed will be set
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

  // alignment but no packing: GCC's `aligned' attribute "can only increase
  // the alignment" of a type or object -- `long m[2] __attribute__((aligned
  // (4)))' keeps its natural 8 -- EXCEPT when it is part of a typedef, where
  // "the aligned attribute can both increase and decrease alignment"
  // (`typedef uint32_t __attribute__((aligned(1))) unaligned_u32;').  The
  // typedef case is marked by the front ends (ID_C_typedef_alignment); the
  // increase-only case falls through to max(n, natural) below.
  if(
    a_int > 0 && !type.get_bool(ID_C_packed) &&
    given_alignment.get_bool(ID_C_typedef_alignment))
  {
    return apply_pragma_pack(type, a_int);
  }
  // alignment and packing: GCC's `aligned' attribute can only increase the
  // alignment, unless `packed' is specified as well, in which case the
  // alignment is exactly the given one (both larger and smaller than the
  // natural one).  `struct S { ... } __attribute__((packed, aligned(16)))'
  // has alignment 16, and a member of that type is placed on a 16-byte
  // boundary.  (#pragma pack(n) is a separate cap, ID_C_pragma_pack, applied
  // on every path by apply_pragma_pack.)
  // (For a packed struct or union the members' OWN `aligned(n)' attributes
  // still count: `struct P { char c; int x __attribute__((aligned(4))); }
  // __attribute__((packed))' has x at offset 4 and alignment 4, and a
  // `packed, aligned(4)' struct with an aligned(8) member has alignment 8.)
  else if(type.get_bool(ID_C_packed))
  {
    mp_integer result = a_int > 0 ? a_int : 1;
    if(type.id() == ID_struct || type.id() == ID_union)
    {
      for(const auto &c : to_struct_union_type(type).components())
      {
        const auto member_alignment = explicit_member_alignment(c.type());
        if(member_alignment.has_value() && *member_alignment > result)
          result = *member_alignment;
        // GCC: a named bit-field of a packed struct declared under
        // `#pragma pack(n)' still contributes min(n, natural) (observed:
        // `struct { short m : 9; bool b[8]; } __attribute__((packed))'
        // under pack(2) has alignment 2)
        if(
          c.type().id() == ID_c_bit_field && !c.get_anonymous() &&
          to_c_bit_field_type(c.type())
            .underlying_type()
            .find(ID_C_pragma_pack)
            .is_not_nil())
        {
          result = std::max(
            result,
            alignment_rec(
              to_c_bit_field_type(c.type()).underlying_type(),
              ns,
              in_progress,
              done));
        }
      }
    }
    return apply_pragma_pack(type, result);
  }

  // compute default
  mp_integer result;

  if(type.id()==ID_array)
    result =
      alignment_rec(to_array_type(type).element_type(), ns, in_progress, done);
  else if(type.id()==ID_struct || type.id()==ID_union)
  {
    result=1;

    // get the max
    // (should really be the smallest common denominator)
    for(const auto &c : to_struct_union_type(type).components())
    {
      // padding is an artefact of the layout, and an unnamed bit-field's
      // type does not affect the alignment (System V ABI)
      if(c.get_is_padding())
        continue;
      if(c.type().id() == ID_c_bit_field && c.get_anonymous())
        continue;
      result = std::max(result, alignment_rec(c.type(), ns, in_progress, done));
    }
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
    result = alignment_rec(
      to_c_enum_type(type).underlying_type(), ns, in_progress, done);
  else if(type.id()==ID_c_enum_tag)
  {
    // The (per-use) alignment/packing adjustment below depends only on
    // this node's ID_C_alignment/ID_C_packed, so memoize the tag's pure
    // alignment to avoid re-following the same tag exponentially through
    // a shared (DAG-shaped) type graph.
    const irep_idt &id = to_c_enum_tag_type(type).get_identifier();
    auto cached = done.find(id);
    if(cached != done.end())
      result = cached->second;
    else if(!in_progress.insert(id).second)
      return 1; // cycle: conservative min alignment
    else
    {
      result = alignment_rec(
        ns.follow_tag(to_c_enum_tag_type(type)), ns, in_progress, done);
      in_progress.erase(id);
      done[id] = result;
    }
  }
  else if(type.id() == ID_struct_tag)
  {
    const irep_idt &id = to_struct_tag_type(type).get_identifier();
    auto cached = done.find(id);
    if(cached != done.end())
      result = cached->second;
    else if(!in_progress.insert(id).second)
      return 1; // cycle: conservative min alignment
    else
    {
      result = alignment_rec(
        ns.follow_tag(to_struct_tag_type(type)), ns, in_progress, done);
      in_progress.erase(id);
      done[id] = result;
    }
  }
  else if(type.id() == ID_union_tag)
  {
    const irep_idt &id = to_union_tag_type(type).get_identifier();
    auto cached = done.find(id);
    if(cached != done.end())
      result = cached->second;
    else if(!in_progress.insert(id).second)
      return 1; // cycle: conservative min alignment
    else
    {
      result = alignment_rec(
        ns.follow_tag(to_union_tag_type(type)), ns, in_progress, done);
      in_progress.erase(id);
      done[id] = result;
    }
  }
  else if(type.id()==ID_c_bit_field)
  {
    // we align these according to the 'underlying type'
    result = alignment_rec(
      to_c_bit_field_type(type).underlying_type(), ns, in_progress, done);
  }
  else
    result=1;

  // aligned(n) without packed: increase only
  if(a_int > result)
    result = a_int;

  return apply_pragma_pack(type, result);
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

/// A padding component's name must be unique within the struct: the
/// components of a (padded) C++ base class are flattened into the derived
/// class together with their `$pad<N>' components, and the derived class's
/// own layout may want the same index.
static irep_idt fresh_padding_name(
  const struct_typet::componentst &components,
  const std::string &prefix,
  std::size_t index)
{
  std::string name = prefix + std::to_string(index);
  auto taken = [&](const std::string &n)
  {
    for(const auto &c : components)
      if(c.get_name() == n)
        return true;
    return false;
  };
  while(taken(name))
    name += "$";
  return name;
}

static struct_typet::componentst::iterator pad_bit_field(
  struct_typet::componentst &components,
  struct_typet::componentst::iterator where,
  std::size_t pad_bits)
{
  const c_bit_field_typet padding_type(
    unsignedbv_typet(pad_bits), pad_bits);

  struct_typet::componentt component(
    fresh_padding_name(
      components, "$bit_field_pad", where - components.begin()),
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
    fresh_padding_name(components, "$pad", where - components.begin()),
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

      if(to_c_bit_field_type(it_type).get_width()==0)
      {
        // A zero-width bit-field causes alignment to the base-type -- its
        // FULL alignment, not capped by #pragma pack(n) (GCC: `#pragma
        // pack(4)' with `char c; long long : 0; char d;' puts d at 8).
        typet underlying = to_c_bit_field_type(it_type).underlying_type();
        underlying.remove(ID_C_pragma_pack);
        a = alignment(underlying, ns);
      }
      else
      {
        // Otherwise, ANSI-C says that bit-fields do not get padded!
        // We consider the type for max_alignment, however -- except in a
        // packed struct (byte-aligned bit-fields) and for UNNAMED bit-fields
        // (System V ABI: "unnamed bit-fields' types do not affect the
        // alignment of a structure or union").
        const bool under_pragma_pack = to_c_bit_field_type(it_type)
                                         .underlying_type()
                                         .find(ID_C_pragma_pack)
                                         .is_not_nil();
        if(
          max_alignment < a && !it->get_anonymous() &&
          (!struct_is_packed || under_pragma_pack))
          max_alignment=a;

        std::size_t w=to_c_bit_field_type(it_type).get_width();

        // System V ABI (and the Itanium C++ ABI): a bit-field must be
        // contained in a storage unit of its declared type, where the
        // storage units are the type-sized slots counted from the start of
        // the struct.  When the bit-field does not fit into what remains of
        // the current unit, it starts at the next one; the remaining bits
        // are padding.  `struct { uint8_t a : 6, b : 1, c : 4, d : 5; }' is
        // thus 3 bytes, not 2.  A packed struct places bit-fields densely.
        // Under `#pragma pack(n)' -- any n -- GCC lays bit-fields out
        // densely, like in a packed struct (`char c; short s : 14; char d;'
        // under pack(8) has d at 3; without the pragma at 4).
        if(!struct_is_packed && !under_pragma_pack && !it->get_is_padding())
        {
          const auto unit_bits =
            underlying_width(to_c_bit_field_type(it_type), ns);
          if(unit_bits.has_value() && *unit_bits > 0)
          {
            const mp_integer position =
              offset * config.ansi_c.char_width + bit_field_bits;
            const mp_integer room = *unit_bits - position % *unit_bits;
            if(room < w)
            {
              const std::size_t pad_bits = numeric_cast_v<std::size_t>(room);
              it = pad_bit_field(components, it, pad_bits);
              bit_field_bits += pad_bits;
              offset += bit_field_bits / config.ansi_c.char_width;
              bit_field_bits %= config.ansi_c.char_width;
            }
          }
        }

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
    else if(struct_is_packed)
    {
      // packed: byte-aligned, unless the MEMBER itself says `aligned(n)'
      // (the alignment of its type is ignored -- an aligned(16) struct
      // member of a packed struct sits at offset 1)
      const auto member_alignment = explicit_member_alignment(it_type);
      a = member_alignment.has_value() ? *member_alignment : 1;
    }
    else
      a=alignment(it_type, ns);

    // complete a run of bit-fields to a byte boundary
    if(bit_field_bits != 0)
    {
      const std::size_t pad_bits = config.ansi_c.char_width - bit_field_bits;
      it = pad_bit_field(components, it, pad_bits);
      bit_field_bits = 0;
      ++offset;
    }

    // check minimum alignment
    if(
      !struct_is_packed && a < config.ansi_c.alignment &&
      !it_type.get_bool(ID_C_packed) &&
      (it_type.id() != ID_struct_tag ||
       !ns.follow_tag(to_struct_tag_type(it_type)).get_bool(ID_C_packed)) &&
      (it_type.id() != ID_union_tag ||
       !ns.follow_tag(to_union_tag_type(it_type)).get_bool(ID_C_packed)))
    {
      a=config.ansi_c.alignment;
    }

    // a zero-width bit-field aligns the next member to its type but, being
    // unnamed, does not raise the struct's alignment
    if(max_alignment < a && it_type.id() != ID_c_bit_field)
      max_alignment=a;

    if(a != 1)
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

  // complete a trailing run of bit-fields (see above)
  if(bit_field_bits != 0)
  {
    const std::size_t pad_bits = config.ansi_c.char_width - bit_field_bits;
    pad_bit_field(components, components.end(), pad_bits);
    bit_field_bits = 0;
    ++offset;
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
  // A packed struct without an alignment specification is padded at the end
  // only to the alignment its explicitly aligned members demand
  // (max_alignment collected above is 1 when there is none).

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
  // A packed union has alignment 1 unless it carries `aligned(n)' or a
  // member does; alignment() above accounts for all of these.

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
