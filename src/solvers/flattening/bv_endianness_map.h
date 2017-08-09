/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_SOLVERS_FLATTENING_BV_ENDIANNESS_MAP_H
#define CPROVER_SOLVERS_FLATTENING_BV_ENDIANNESS_MAP_H

#include <util/endianness_map.h>

class boolbv_widtht;

/// Map bytes according to the configured endianness. The key difference to
/// endianness_mapt is that bv_endianness_mapt is aware of the bit-level
/// encoding of types, which need not co-incide with the bit layout at
/// source-code level.
class bv_endianness_mapt : public endianness_mapt
{
public:
  bv_endianness_mapt(
    const typet &type,
    bool little_endian,
    const namespacet &_ns,
    boolbv_widtht &_boolbv_width)
    : endianness_mapt(_ns), boolbv_width(_boolbv_width)
  {
    build(type, little_endian);
  }

protected:
  boolbv_widtht &boolbv_width;

  virtual void build_little_endian(const typet &type) override;
  virtual void build_big_endian(const typet &type) override;
};

#endif // CPROVER_SOLVERS_FLATTENING_BV_ENDIANNESS_MAP_H
