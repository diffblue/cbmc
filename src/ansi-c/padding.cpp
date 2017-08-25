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

  mp_integer a_int;

  // we trust it blindly, no matter how nonsensical
  if(given_alignment.is_nil() ||
     to_integer(given_alignment, a_int))
    a_int=0;

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
    const struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    result=1;

    // get the max
    // (should really be the smallest common denominator)
    for(struct_union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
      result=std::max(result, alignment(it->type(), ns));
  }
  else if(type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_c_bool)
  {
    std::size_t width=to_bitvector_type(type).get_width();
    result=width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_c_enum)
    result=alignment(type.subtype(), ns);
  else if(type.id()==ID_c_enum_tag)
    result=alignment(ns.follow_tag(to_c_enum_tag_type(type)), ns);
  else if(type.id()==ID_pointer)
  {
    std::size_t width=config.ansi_c.pointer_width;
    result=width%8?width/8+1:width/8;
  }
  else if(type.id()==ID_symbol)
    result=alignment(ns.follow(type), ns);
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

void add_padding(struct_typet &type, const namespacet &ns)
{
  struct_typet::componentst &components=type.components();

  // First do padding for bit-fields to make them
  // appear on byte boundaries.

  {
    std::size_t padding_counter=0;
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
        std::size_t width=to_c_bit_field_type(it->type()).get_width();
        bit_field_bits+=width;
      }
      else if(bit_field_bits!=0)
      {
        // not on a byte-boundary?
        if((bit_field_bits%8)!=0)
        {
          std::size_t pad=8-bit_field_bits%8;
          c_bit_field_typet padding_type(unsignedbv_typet(pad), pad);

          struct_typet::componentt component;
          component.type()=padding_type;
          component.set_name(
            "$bit_field_pad"+std::to_string(padding_counter++));
          component.set_is_padding(true);

          it=components.insert(it, component);
          it++; // skip over

          bit_field_bits+=pad;
        }

        bit_field_bits=0;
      }
    }

    // Add padding at the end?
    if((bit_field_bits%8)!=0)
    {
      std::size_t pad=8-bit_field_bits%8;
      c_bit_field_typet padding_type(unsignedbv_typet(pad), pad);

      struct_typet::componentt component;
      component.type()=padding_type;
      component.set_name("$bit_field_pad"+std::to_string(padding_counter++));
      component.set_is_padding(true);

      components.push_back(component);
    }
  }

  // Is the struct packed, without any alignment specification?
  if(type.get_bool(ID_C_packed) &&
     type.find(ID_C_alignment).is_nil())
    return; // done

  mp_integer offset=0;
  std::size_t padding_counter=0;
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
        std::size_t bytes;
        for(bytes=0; w>bit_field_bits; ++bytes, bit_field_bits+=8) {}
        bit_field_bits-=w;
        offset+=bytes;
        continue;
      }
    }
    else
      a=alignment(it_type, ns);

    // check minimum alignment
    if(a<config.ansi_c.alignment && !packed)
      a=config.ansi_c.alignment;

    if(max_alignment<a)
      max_alignment=a;

    if(a!=1)
    {
      // we may need to align it
      mp_integer displacement=offset%a;

      if(displacement!=0)
      {
        mp_integer pad=a-displacement;

        unsignedbv_typet padding_type;
        padding_type.set_width(integer2unsigned(pad*8));

        struct_typet::componentt component;
        component.type()=padding_type;
        component.set_name("$pad"+std::to_string(padding_counter++));
        component.set_is_padding(true);

        it=components.insert(it, component);
        it++; // skip over

        offset+=pad;
      }
    }

    mp_integer size=pointer_offset_size(it_type, ns);

    if(size!=-1)
      offset+=size;
  }

  if(bit_field_bits!=0)
  {
    // these are now assumed to be multiples of 8
    offset+=bit_field_bits/8;
  }

  // any explicit alignment for the struct?
  if(type.find(ID_C_alignment).is_not_nil())
  {
    const exprt &alignment=
      static_cast<const exprt &>(type.find(ID_C_alignment));
    if(alignment.id()!=ID_default)
    {
      exprt tmp=alignment;
      simplify(tmp, ns);
      mp_integer tmp_i;
      if(!to_integer(tmp, tmp_i) && tmp_i>max_alignment)
        max_alignment=tmp_i;
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
      mp_integer pad=max_alignment-displacement;

      unsignedbv_typet padding_type;
      padding_type.set_width(integer2unsigned(pad*8));

      // we insert after any final 'flexible member'
      struct_typet::componentt component;
      component.type()=padding_type;
      component.set_name("$pad"+std::to_string(padding_counter++));
      component.set_is_padding(true);

      components.push_back(component);
    }
  }
}

void add_padding(union_typet &type, const namespacet &ns)
{
  mp_integer max_alignment=alignment(type, ns)*8;
  mp_integer size_bits=pointer_offset_bits(type, ns);

  if(size_bits<0)
    throw "type of unknown size:\n"+type.pretty();

  union_typet::componentst &components=type.components();

  // Is the union packed?
  if(type.get_bool(ID_C_packed))
  {
    // The size needs to be a multiple of 8 only.
    max_alignment=8;
  }

  // The size must be a multiple of the alignment, or
  // we add a padding member to the union.

  if(size_bits%max_alignment!=0)
  {
    mp_integer padding=max_alignment-(size_bits%max_alignment);

    unsignedbv_typet padding_type;
    padding_type.set_width(integer2unsigned(size_bits+padding));

    struct_typet::componentt component;
    component.type()=padding_type;
    component.set_name("$pad");
    component.set_is_padding(true);

    components.push_back(component);
  }
}
