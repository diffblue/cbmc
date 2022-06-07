/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_width.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/std_types.h>

boolbv_widtht::boolbv_widtht(const namespacet &_ns):ns(_ns)
{
}

const boolbv_widtht::entryt &boolbv_widtht::get_entry(const typet &type) const
{
  // check cache first

  std::pair<cachet::iterator, bool> cache_result =
    cache.emplace(type, entryt{});

  auto &cache_entry = cache_result.first->second;

  if(!cache_result.second) // found!
    return cache_entry;

  const irep_idt type_id=type.id();

  if(type_id==ID_struct)
  {
    const struct_typet::componentst &components=
      to_struct_type(type).components();

    std::size_t offset=0;
    defined_entryt entry{0};
    entry.members.resize(components.size());

    for(std::size_t i=0; i<entry.members.size(); i++)
    {
      auto sub_width = get_width_opt(components[i].type());
      if(!sub_width.has_value())
        return cache_entry;
      entry.members[i].offset=offset;
      entry.members[i].width = *sub_width;
      offset += *sub_width;
    }

    entry.total_width=offset;

    cache_entry = std::move(entry);
  }
  else if(type_id==ID_union)
  {
    const union_typet::componentst &components=
      to_union_type(type).components();

    defined_entryt entry{0};
    entry.members.resize(components.size());

    std::size_t max_width=0;

    for(std::size_t i=0; i<entry.members.size(); i++)
    {
      auto sub_width = get_width_opt(components[i].type());
      if(!sub_width.has_value())
        return cache_entry;
      entry.members[i].width = *sub_width;
      max_width = std::max(max_width, *sub_width);
    }

    entry.total_width=max_width;

    cache_entry = std::move(entry);
  }
  else if(type_id==ID_bool)
  {
    cache_entry = defined_entryt{1};
  }
  else if(type_id==ID_c_bool)
  {
    cache_entry = defined_entryt{to_c_bool_type(type).get_width()};
  }
  else if(type_id==ID_signedbv)
  {
    cache_entry = defined_entryt{to_signedbv_type(type).get_width()};
  }
  else if(type_id==ID_unsignedbv)
  {
    cache_entry = defined_entryt{to_unsignedbv_type(type).get_width()};
  }
  else if(type_id==ID_floatbv)
  {
    cache_entry = defined_entryt{to_floatbv_type(type).get_width()};
  }
  else if(type_id==ID_fixedbv)
  {
    cache_entry = defined_entryt{to_fixedbv_type(type).get_width()};
  }
  else if(type_id==ID_bv)
  {
    cache_entry = defined_entryt{to_bv_type(type).get_width()};
  }
  else if(type_id==ID_verilog_signedbv ||
          type_id==ID_verilog_unsignedbv)
  {
    // we encode with two bits
    std::size_t size = to_bitvector_type(type).get_width();
    DATA_INVARIANT(
      size > 0, "verilog bitvector width shall be greater than zero");
    cache_entry = defined_entryt{size * 2};
  }
  else if(type_id==ID_range)
  {
    mp_integer from=string2integer(type.get_string(ID_from)),
                 to=string2integer(type.get_string(ID_to));

    mp_integer size=to-from+1;

    if(size < 0)
      return cache_entry;
    else if(size == 0)
      cache_entry = defined_entryt{0};
    else
      cache_entry = defined_entryt{address_bits(size)};
  }
  else if(type_id==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    auto sub_width = get_width_opt(array_type.element_type());
    if(!sub_width.has_value())
      return cache_entry;

    const auto array_size = numeric_cast<mp_integer>(array_type.size());

    if(!array_size.has_value() || *array_size < 0)
      return cache_entry;

    mp_integer total = *array_size * *sub_width;
    if(total > (1 << 30)) // realistic limit
      throw analysis_exceptiont("array too large for flattening");
    else
      cache_entry = defined_entryt{numeric_cast_v<std::size_t>(total)};
  }
  else if(type_id==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);
    auto sub_width = get_width_opt(vector_type.element_type());
    if(!sub_width.has_value())
      return cache_entry;

    const auto vector_size = numeric_cast_v<mp_integer>(vector_type.size());

    mp_integer total = vector_size * *sub_width;
    if(total > (1 << 30)) // realistic limit
      throw analysis_exceptiont("vector too large for flattening");
    else
      cache_entry = defined_entryt{numeric_cast_v<std::size_t>(total)};
  }
  else if(type_id==ID_complex)
  {
    auto sub_width = get_width_opt(to_complex_type(type).subtype());
    if(!sub_width.has_value())
      return cache_entry;
    cache_entry =
      defined_entryt{numeric_cast_v<std::size_t>(2 * mp_integer{*sub_width})};
  }
  else if(type_id==ID_code)
  {
    cache_entry = defined_entryt{0};
  }
  else if(type_id==ID_enumeration)
  {
    // get number of necessary bits
    std::size_t size=to_enumeration_type(type).elements().size();
    if(size == 0)
      cache_entry = defined_entryt{0};
    else
      cache_entry = defined_entryt{address_bits(size)};
  }
  else if(type_id==ID_c_enum)
  {
    // these have a subtype
    cache_entry = defined_entryt{
      to_bitvector_type(to_c_enum_type(type).underlying_type()).get_width()};
    CHECK_RETURN(cache_entry->total_width > 0);
  }
  else if(type_id==ID_pointer)
  {
    cache_entry =
      defined_entryt{type_checked_cast<pointer_typet>(type).get_width()};
  }
  else if(type_id==ID_struct_tag)
  {
    cache_entry = get_entry(ns.follow_tag(to_struct_tag_type(type)));
  }
  else if(type_id==ID_union_tag)
  {
    cache_entry = get_entry(ns.follow_tag(to_union_tag_type(type)));
  }
  else if(type_id==ID_c_enum_tag)
  {
    cache_entry = get_entry(ns.follow_tag(to_c_enum_tag_type(type)));
  }
  else if(type_id==ID_c_bit_field)
  {
    cache_entry = defined_entryt{to_c_bit_field_type(type).get_width()};
  }
  else if(type_id==ID_string)
  {
    cache_entry = defined_entryt{32};
  }
  else if(type_id == ID_empty)
  {
    cache_entry = defined_entryt{0};
  }
  else
    UNIMPLEMENTED;

  return cache_entry;
}

const boolbv_widtht::membert &boolbv_widtht::get_member(
  const struct_typet &type,
  const irep_idt &member) const
{
  const auto &entry_opt = get_entry(type);
  CHECK_RETURN(entry_opt.has_value());
  std::size_t component_number=type.component_number(member);
  PRECONDITION(entry_opt->members.size() > component_number);

  return entry_opt->members[component_number];
}
