/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <config.h>
#include <std_types.h>
#include <bitvector.h>

#include "boolbv_width.h"

/*******************************************************************\

Function: boolbv_widtht::boolbv_widtht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolbv_widtht::boolbv_widtht(const namespacet &_ns):ns(_ns)
{
  cache=new cachet;
}

/*******************************************************************\

Function: boolbv_widtht::~boolbv_widtht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolbv_widtht::~boolbv_widtht()
{
  delete cache;
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
    cache->insert(std::pair<typet, entryt>(type, entryt()));
    
  entryt &entry=cache_result.first->second;

  if(!cache_result.second) // found!
    return entry;
    
  entry.total_width=0;

  if(type.id()==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    unsigned offset=0;
    entry.members.resize(components.size());
  
    for(unsigned i=0; i<entry.members.size(); i++)
    {
      unsigned sub_width=operator()(components[i].type());
      entry.members[i].offset=offset;
      entry.members[i].width=sub_width;
      offset+=sub_width;
    }
    
    entry.total_width=offset;
  }
  else if(type.id()==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    entry.members.resize(components.size());
    
    unsigned max_width=0;
  
    for(unsigned i=0; i<entry.members.size(); i++)
    {
      unsigned sub_width=operator()(components[i].type());
      entry.members[i].width=sub_width;
      max_width=std::max(max_width, sub_width);
    }

    entry.total_width=max_width;
  }
  else if(type.id()==ID_bool)
    entry.total_width=1;
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_bv)
  {
    entry.total_width=bv_width(type);
    assert(entry.total_width!=0);
  }
  else if(type.id()==ID_verilogbv)
  {
    // we encode with two bits
    entry.total_width=type.get_int(ID_width)*2;
    assert(entry.total_width!=0);
  }
  else if(type.id()==ID_range)
  {
    mp_integer from=string2integer(type.get_string(ID_from)),
                 to=string2integer(type.get_string(ID_to));

    mp_integer size=to-from+1;

    if(size>=1)
    {
      entry.total_width=integer2long(address_bits(size));
      assert(entry.total_width!=0);
    }
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    unsigned sub_width=operator()(array_type.subtype());

    mp_integer array_size;

    if(to_integer(array_type.size(), array_size))
    {
      // we can still use the theory of arrays for this
      entry.total_width=0;
    }
    else
      entry.total_width=integer2long(array_size*sub_width);
  }
  else if(type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);
    unsigned sub_width=operator()(vector_type.subtype());

    mp_integer vector_size;

    if(to_integer(vector_type.size(), vector_size))
    {
      // we can still use the theory of arrays for this
      entry.total_width=0;
    }
    else
      entry.total_width=integer2long(vector_size*sub_width);
  }
  else if(type.id()==ID_code)
  {
  }
  else if(type.id()==ID_enum)
  {
    // get number of necessary bits

    unsigned size=type.find(ID_elements).get_sub().size();
    entry.total_width=integer2long(address_bits(size));
    assert(entry.total_width!=0);
  }
  else if(type.id()==ID_c_enum ||
          type.id()==ID_incomplete_c_enum)
  {
    entry.total_width=type.get_int(ID_width);
    assert(entry.total_width!=0);
  }
  else if(type.id()==ID_pointer ||
          type.id()==ID_reference)
  {
    entry.total_width=config.ansi_c.pointer_width;
  }
  else if(type.id()==ID_symbol)
    entry=get_entry(ns.follow(type));
  
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

/*******************************************************************\

Function: boolbv_get_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
bool boolbv_get_width(
  const typet &type,
  unsigned &width,
  const namespacet &ns)
{
  boolbv_widtht boolbv_width(ns);
  width=boolbv_width(type);
  return false;
}

/*******************************************************************\

Function: boolbv_member_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool boolbv_member_offset(
  const struct_typet &type,
  const irep_idt &member,
  unsigned &width,
  const namespacet &ns)
{
  boolbv_widtht boolbv_width(ns);
  return boolbv_width.get_member(type, member).offset;
}
#endif
