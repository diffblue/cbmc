/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_ENDIANNESS_MAP_H
#define CPROVER_UTIL_ENDIANNESS_MAP_H

/*! \file util/byte_operators.h
 * \brief Expression classes for byte-level operators
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include <cassert>
#include <vector>

#include "expr.h"

class namespacet;

/*! \brief Maps a big-endian offset to a little-endian offset
*/
class endianness_mapt
{
public:
  inline endianness_mapt(
    const typet &type,
    bool little_endian,
    const namespacet &_ns):ns(_ns)
  {
    build(type, little_endian);
  }

  inline size_t map_bit(size_t bit) const
  {
    assert(bit<map.size());
    size_t result=map[bit];
    assert(result<map.size());
    return result;
  }
  
  inline size_t number_of_bits() const
  {
    return map.size();
  }
  
  void build(const typet &type, bool little_endian);
  
  void output(std::ostream &) const;

protected:
  const namespacet &ns;
  std::vector<size_t> map; // bit-nr to bit-nr

  void build_little_endian(const typet &type);
  void build_big_endian(const typet &type);
};

extern inline std::ostream &operator << (
  std::ostream &out,
  const endianness_mapt &m)
{
  m.output(out);
  return out;
}

#endif
