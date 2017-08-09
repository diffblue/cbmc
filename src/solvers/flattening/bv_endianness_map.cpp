/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "bv_endianness_map.h"

#include <util/arith_tools.h>
#include <util/c_types.h>

#include "boolbv_width.h"

void bv_endianness_mapt::build_little_endian(const typet &src)
{
  const std::size_t width = boolbv_width(src);

  if(width == 0)
    return;

  const std::size_t new_size = map.size() + width;
  map.reserve(new_size);

  for(std::size_t i = map.size(); i < new_size; ++i)
    map.push_back(i);
}

void bv_endianness_mapt::build_big_endian(const typet &src)
{
  if(src.id() == ID_pointer)
    build_little_endian(src);
  else
    endianness_mapt::build_big_endian(src);
}
