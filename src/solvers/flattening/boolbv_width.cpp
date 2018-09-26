/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_width.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/std_types.h>

boolbv_widtht::boolbv_widtht(const namespacet &_ns):ns(_ns)
{
}

boolbv_widtht::~boolbv_widtht()
{
}

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
  }
  else if(type_id==ID_signedbv)
  {
    entry.total_width=to_signedbv_type(type).get_width();
  }
  else if(type_id==ID_unsignedbv)
  {
    entry.total_width=to_unsignedbv_type(type).get_width();
  }
  else if(type_id==ID_floatbv)
  {
    entry.total_width=to_floatbv_type(type).get_width();
  }
  else if(type_id==ID_fixedbv)
  {
    entry.total_width=to_fixedbv_type(type).get_width();
  }
  else if(type_id==ID_bv)
  {
    entry.total_width=to_bv_type(type).get_width();
  }
  else if(type_id==ID_verilog_signedbv ||
          type_id==ID_verilog_unsignedbv)
  {
    // we encode with two bits
    std::size_t size = type.get_size_t(ID_width);
    DATA_INVARIANT(
      size > 0, "verilog bitvector width shall be greater than zero");
    entry.total_width = size * 2;
  }
  else if(type_id==ID_range)
  {
    mp_integer from=string2integer(type.get_string(ID_from)),
                 to=string2integer(type.get_string(ID_to));

    mp_integer size=to-from+1;

    if(size>=1)
    {
      entry.total_width = address_bits(size);
      CHECK_RETURN(entry.total_width > 0);
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
        throw analysis_exceptiont("array too large for flattening");

      entry.total_width = numeric_cast_v<std::size_t>(total);
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
        analysis_exceptiont("vector too large for flattening");

      entry.total_width = numeric_cast_v<std::size_t>(vector_size * sub_width);
    }
  }
  else if(type_id==ID_complex)
  {
    const mp_integer sub_width = operator()(type.subtype());
    entry.total_width = numeric_cast_v<std::size_t>(2 * sub_width);
  }
  else if(type_id==ID_code)
  {
  }
  else if(type_id==ID_enumeration)
  {
    // get number of necessary bits
    std::size_t size=to_enumeration_type(type).elements().size();
    entry.total_width = address_bits(size);
    CHECK_RETURN(entry.total_width > 0);
  }
  else if(type_id==ID_c_enum)
  {
    // these have a subtype
    entry.total_width = type.subtype().get_size_t(ID_width);
    CHECK_RETURN(entry.total_width > 0);
  }
  else if(type_id==ID_incomplete_c_enum)
  {
    // no width
  }
  else if(type_id==ID_pointer)
    entry.total_width = type_checked_cast<pointer_typet>(type).get_width();
  else if(type_id == ID_symbol_type)
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
  else if(type_id==ID_string)
    entry.total_width=32;
  else if(type_id != ID_empty)
    UNIMPLEMENTED;

  return entry;
}

const boolbv_widtht::membert &boolbv_widtht::get_member(
  const struct_typet &type,
  const irep_idt &member) const
{
  std::size_t component_number=type.component_number(member);

  return get_entry(type).members[component_number];
}
