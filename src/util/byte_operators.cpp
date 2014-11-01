/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>
#include <cassert>

#include "std_types.h"
#include "pointer_offset_size.h"
#include "arith_tools.h"
#include "byte_operators.h"
#include "namespace.h"
#include "config.h"

/*******************************************************************\

Function: byte_extract_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt byte_extract_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::IS_LITTLE_ENDIAN:
    return ID_byte_extract_little_endian;

  case configt::ansi_ct::IS_BIG_ENDIAN:
    return ID_byte_extract_big_endian;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: byte_update_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt byte_update_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::IS_LITTLE_ENDIAN:
    return ID_byte_update_little_endian;

  case configt::ansi_ct::IS_BIG_ENDIAN:
    return ID_byte_update_big_endian;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: endianness_mapt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::output(std::ostream &out) const
{
  for(std::vector<size_t>::const_iterator it=map.begin();
      it!=map.end();
      ++it)
  {
    if(it!=map.begin()) out << ", ";
    out << *it;
  }
}

/*******************************************************************\

Function: endianness_mapt::build_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::build_rec(
  const typet &src,
  bool little_endian,
  size_t &bit_field_bits)
{
  if(little_endian)
  {
    mp_integer s=pointer_offset_size(ns, src); // error is -1
    while(s>0)
    {
      map.push_back(map.size());
      --s;
    }
    return;
  }  

  if(src.id()==ID_symbol)
    build_rec(ns.follow(src), little_endian, bit_field_bits);
  else if(src.id()==ID_c_enum_tag)
    build_rec(
      ns.follow_tag(to_c_enum_tag_type(src)),
      little_endian,
      bit_field_bits);
  else if(src.id()==ID_unsignedbv ||
          src.id()==ID_signedbv ||
          src.id()==ID_fixedbv ||
          src.id()==ID_floatbv ||
          src.id()==ID_c_enum)
  {
    mp_integer s=pointer_offset_size(ns, src); // error is -1
    assert(s>=0);

    size_t s_int=integer2long(s), base=map.size();

    // from struct_union_typet::componentt::get_bit_field_bits
    size_t bits=8*s_int;
    if(src.id()==ID_signedbv ||
       src.id()==ID_unsignedbv)
      bits=to_bitvector_type(src).get_width();
    else if(src.id()==ID_c_enum)
      bits=src.subtype().get_int(ID_width);

    assert(bit_field_bits<8);
    if((bit_field_bits+bits)%8==0)
      bit_field_bits=0;
    else if(bit_field_bits+bits<8)
    {
      // keep accumulating
      bit_field_bits+=bits;
      if(s>0) --s_int;
    }
    else
    {
      bit_field_bits+=bits;
      if(bit_field_bits<s_int*8) --s_int;
      bit_field_bits%=8;
    }

    for(size_t i=0; i<s_int; i++)
    {
      if(little_endian)
        map.push_back(base+i);
      else
        map.push_back(base+s_int-i-1); // these do get re-ordered!
    }
  }
  else if(src.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(src);

    // todo: worry about padding being in wrong order
    for(struct_typet::componentst::const_iterator
        it=struct_type.components().begin();
        it!=struct_type.components().end();
        it++)
      build_rec(it->type(), little_endian, bit_field_bits);
  }
  else if(src.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src);

    // array size constant?
    mp_integer s;
    if(!to_integer(array_type.size(), s))
    {
      while(s>0)
      {
        build_rec(array_type.subtype(), little_endian, bit_field_bits);
        --s;
      }
    }
  }
  else
  {
    // everything else (unions in particular)
    // is treated like a byte-array
    mp_integer s=pointer_offset_size(ns, src); // error is -1
    while(s>0)
    {
      map.push_back(map.size());
      --s;
    }
  }
}
