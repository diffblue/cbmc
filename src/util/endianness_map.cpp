/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "endianness_map.h"

#include <ostream>

#include "std_types.h"
#include "pointer_offset_size.h"
#include "arith_tools.h"
#include "namespace.h"

void endianness_mapt::output(std::ostream &out) const
{
  for(std::vector<size_t>::const_iterator it=map.begin();
      it!=map.end();
      ++it)
  {
    if(it!=map.begin())
      out << ", ";
    out << *it;
  }
}

void endianness_mapt::build(const typet &src, bool little_endian)
{
  if(little_endian)
    build_little_endian(src);
  else
    build_big_endian(src);
}

void endianness_mapt::build_little_endian(const typet &src)
{
  auto s = pointer_offset_bits(src, ns);

  if(!s.has_value())
    return;

  const std::size_t new_size = map.size() + numeric_cast_v<std::size_t>(*s);
  map.reserve(new_size);

  for(std::size_t i=map.size(); i<new_size; ++i)
    map.push_back(i);
}

void endianness_mapt::build_big_endian(const typet &src)
{
  if(src.id() == ID_symbol_type)
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
    auto bits = pointer_offset_bits(src, ns); // error is -1
    CHECK_RETURN(bits.has_value());

    const std::size_t bits_int = numeric_cast_v<std::size_t>(*bits);
    const std::size_t base = map.size();

    for(size_t bit=0; bit<bits_int; bit++)
    {
      map.push_back(base+bits_int-1-bit);
    }
  }
  else if(src.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(src);

    // todo: worry about padding being in wrong order
    for(const auto &c : struct_type.components())
    {
      build_big_endian(c.type());
    }
  }
  else if(src.id() == ID_struct_tag)
  {
    build_big_endian(ns.follow_tag(to_struct_tag_type(src)));
  }
  else if(src.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(src);

    // array size constant?
    auto s = numeric_cast<mp_integer>(array_type.size());
    if(s.has_value())
    {
      while(*s > 0)
      {
        build_big_endian(array_type.subtype());
        --(*s);
      }
    }
  }
  else if(src.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(src);

    mp_integer s = numeric_cast_v<mp_integer>(vector_type.size());

    while(s > 0)
    {
      build_big_endian(vector_type.subtype());
      --s;
    }
  }
  else
  {
    // everything else (unions in particular)
    // is treated like a byte-array
    auto s = pointer_offset_bits(src, ns); // error is -1

    if(!s.has_value())
      return;

    const std::size_t new_size = map.size() + numeric_cast_v<std::size_t>(*s);
    map.reserve(new_size);

    for(std::size_t i=map.size(); i<new_size; ++i)
      map.push_back(i);
  }
}
