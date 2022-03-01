/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_ENDIANNESS_MAP_WIDE_H
#define CPROVER_CPROVER_ENDIANNESS_MAP_WIDE_H

#include <util/endianness_map.h>

class endianness_map_widet : public endianness_mapt
{
public:
  endianness_map_widet(
    const typet &type,
    bool little_endian,
    const namespacet &_ns)
    : endianness_mapt(type, little_endian, _ns)
  {
  }

protected:
  void build_little_endian(const typet &) override;
};

#endif // CPROVER_CPROVER_ENDIANNESS_MAP_WIDE_H
