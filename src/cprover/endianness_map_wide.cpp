/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "endianness_map_wide.h"

#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/type.h>

void endianness_map_widet::build_little_endian(const typet &src)
{
  if(src.id() == ID_pointer)
  {
    auto s = pointer_offset_bits(src, ns);
    CHECK_RETURN(s.has_value());
    s.value() = s.value() * 2;

    const std::size_t new_size = map.size() + numeric_cast_v<std::size_t>(*s);
    map.reserve(new_size);

    for(std::size_t i = map.size(); i < new_size; ++i)
      map.push_back(i);
  }
  else
    endianness_mapt::build_little_endian(src);
}
