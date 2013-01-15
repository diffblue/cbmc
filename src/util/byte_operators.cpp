/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <pointer_offset_size.h>
#include <arith_tools.h>

#include "byte_operators.h"
#include "namespace.h"

/*******************************************************************\

Function: endianness_mapt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::output(std::ostream &out) const
{
  for(unsigned i=0; i<map.size(); i++)
  {
    if(i!=0) out << ", ";
    out << map[i];
  }
}

/*******************************************************************\

Function: endianness_mapt::build_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void endianness_mapt::build_rec(const typet &src, bool little_endian)
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
    build_rec(ns.follow(src), little_endian);
  else if(src.id()==ID_unsignedbv ||
          src.id()==ID_signedbv ||
          src.id()==ID_fixedbv ||
          src.id()==ID_floatbv ||
          src.id()==ID_c_enum)
  {
    mp_integer s=pointer_offset_size(ns, src); // error is -1
    unsigned s_int=integer2long(s), base=map.size();

    for(unsigned i=0; i<s_int; i++)
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
    {
      // todo: worry about non-byte granularity bitfields
    
      build_rec(it->type(), little_endian);
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
        build_rec(array_type.subtype(), little_endian);
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
