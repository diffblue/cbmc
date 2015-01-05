/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/std_types.h>
#include <util/bitvector.h>

#include "boolbv_width.h"

/*******************************************************************\

Function: boolbv_widtht::boolbv_widtht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolbv_widtht::boolbv_widtht(const namespacet &_ns):ns(_ns)
{
}

/*******************************************************************\

Function: boolbv_widtht::~boolbv_widtht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolbv_widtht::~boolbv_widtht()
{
}

/*******************************************************************\

Function: boolbv_widtht::get_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const boolbv_widtht::entryt &boolbv_widtht::get_entry(const typet &type) const
{
  // check cache first

  std::pair<cachet::iterator, bool> cache_result=
    cache.insert(std::pair<typet, entryt>(type, entryt()));
    
  entryt &entry=cache_result.first->second;

  if(!cache_result.second) // found!
    return entry;
    
  entry.total_width=0;
  
  const irep_idt type_id=type.id();

  if(type_id==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    std::size_t offset=0;
    entry.members.resize(components.size());
  
    for(std::size_t i=0; i<entry.members.size(); i++)
    {
      std::size_t sub_width=operator()(components[i].type());
      entry.members[i].offset=offset;
      entry.members[i].width=sub_width;
      offset+=sub_width;
    }
    
    entry.total_width=offset;
  }
  else if(type_id==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    entry.members.resize(components.size());
    
    std::size_t max_width=0;
  
    for(std::size_t i=0; i<entry.members.size(); i++)
    {
      std::size_t sub_width=operator()(components[i].type());
      entry.members[i].width=sub_width;
      max_width=std::max(max_width, sub_width);
    }

    entry.total_width=max_width;
  }
  else if(type_id==ID_bool)
    entry.total_width=1;
  else if(type_id==ID_c_bool)
  {
    entry.total_width=to_c_bool_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_signedbv)
  {
    entry.total_width=to_signedbv_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_unsignedbv)
  {
    entry.total_width=to_unsignedbv_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_floatbv)
  {
    entry.total_width=to_floatbv_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_fixedbv)
  {
    entry.total_width=to_fixedbv_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_bv)
  {
    entry.total_width=to_bv_type(type).get_width();
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_verilogbv)
  {
    // we encode with two bits
    entry.total_width=type.get_unsigned_int(ID_width)*2;
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_range)
  {
    mp_integer from=string2integer(type.get_string(ID_from)),
                 to=string2integer(type.get_string(ID_to));

    mp_integer size=to-from+1;

    if(size>=1)
    {
      entry.total_width=integer2unsigned(address_bits(size));
      assert(entry.total_width!=0);
    }
  }
  else if(type_id==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    std::size_t sub_width=operator()(array_type.subtype());

    mp_integer array_size;

    if(to_integer(array_type.size(), array_size))
    {
      // we can still use the theory of arrays for this
      entry.total_width=0;
    }
    else
    {
      mp_integer total=array_size*sub_width;
      if(total>(1<<30)) // realistic limit
        throw "array too large for flattening";

      entry.total_width=integer2unsigned(total);
    }
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);
    std::size_t sub_width=operator()(vector_type.subtype());

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      // we can still use the theory of arrays for this
      entry.total_width=0;
    }
    else
    {
      mp_integer total=vector_size*sub_width;
      if(total>(1<<30)) // realistic limit
        throw "vector too large for flattening";

      entry.total_width=integer2unsigned(vector_size*sub_width);
    }
  }
  else if(type_id==ID_complex)
  {
    std::size_t sub_width=operator()(type.subtype());
    entry.total_width=integer2unsigned(2*sub_width);
  }
  else if(type_id==ID_code)
  {
  }
  else if(type_id==ID_enum)
  {
    // get number of necessary bits

    std::size_t size=type.find(ID_elements).get_sub().size();
    entry.total_width=integer2unsigned(address_bits(size));
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_c_enum)
  {
    // these have a subtype
    entry.total_width=type.subtype().get_unsigned_int(ID_width);
    assert(entry.total_width!=0);
  }
  else if(type_id==ID_incomplete_c_enum)
  {
    // no width
  }
  else if(type_id==ID_pointer ||
          type_id==ID_reference)
  {
    entry.total_width=config.ansi_c.pointer_width;
  }
  else if(type_id==ID_symbol)
    entry=get_entry(ns.follow(type));
  else if(type_id==ID_struct_tag)
    entry=get_entry(ns.follow_tag(to_struct_tag_type(type)));
  else if(type_id==ID_union_tag)
    entry=get_entry(ns.follow_tag(to_union_tag_type(type)));
  else if(type_id==ID_c_enum_tag)
    entry=get_entry(ns.follow_tag(to_c_enum_tag_type(type)));
  else if(type_id==ID_c_bit_field)
  {
    entry.total_width=to_c_bit_field_type(type).get_width();
  }
  
  return entry;
}

/*******************************************************************\

Function: boolbv_widtht::get_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const boolbv_widtht::membert &boolbv_widtht::get_member(
  const struct_typet &type,
  const irep_idt &member) const
{
  unsigned component_number=type.component_number(member);

  return get_entry(type).members[component_number];
}
