/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>
#include <cassert>

#include "std_types.h"
#include "pointer_offset_size.h"
#include "arith_tools.h"
#include "endianness_map.h"
#include "namespace.h"

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

Function: endianness_mapt::build_little_endian

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::build_little_endian(const typet &src)
{
  mp_integer s=pointer_offset_bits(src, ns); // error is -1
  
  while(s>0)
  {
    map.push_back(map.size());
    --s;
  }

  #if 0
  // we make sure we have byte granularity
  while(map.size()%8!=0)
    map.push_back(map.size());
  #endif
}

/*******************************************************************\

Function: endianness_mapt::build_big_endian

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::build_big_endian(const typet &src)
{
  build_big_endian_rec(src);

  #if 0
  // we make sure we have byte granularity
  while(map.size()%8!=0)
    map.push_back(map.size());
  #endif
}

/*******************************************************************\

Function: endianness_mapt::build_big_endian_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::build_big_endian_rec(const typet &src)
{
  if(src.id()==ID_symbol)
    build_big_endian(ns.follow(src));
  else if(src.id()==ID_c_enum_tag)
    build_big_endian(ns.follow_tag(to_c_enum_tag_type(src)));
  else if(src.id()==ID_unsignedbv ||
          src.id()==ID_signedbv ||
          src.id()==ID_fixedbv ||
          src.id()==ID_floatbv ||
          src.id()==ID_c_enum ||
          src.id()==ID_c_bit_field)
  {
    // these do get re-ordered!
    mp_integer bits=pointer_offset_bits(src, ns); // error is -1
    assert(bits>=0);

    size_t bits_int=integer2long(bits), base=map.size();
    size_t bytes_int=bits_int/8+((bits_int%8)!=0?1:0);

    for(size_t bit=0; bit<bits_int; bit++)
    {
      size_t byte=bit/8;
      size_t mapped_byte=bytes_int-1-byte;
      map.push_back(base+mapped_byte*8+bit%8);
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
    {
      build_big_endian(it->type());
    }
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
        build_big_endian(array_type.subtype());
        --s;
      }
    }
  }
  else
  {
    // everything else (unions in particular)
    // is treated like a byte-array
    mp_integer s=pointer_offset_bits(src, ns); // error is -1
    while(s>0)
    {
      map.push_back(map.size());
      --s;
    }
  }
}
