/*******************************************************************\

Module: Sparse Vectors

Author: Romain Brenguier

\*******************************************************************/

/// \file
/// Sparse Vectors

#ifndef CPROVER_UTIL_SPARSE_VECTOR_H
#define CPROVER_UTIL_SPARSE_VECTOR_H

#include "invariant.h"
#include "mp_arith.h"

#include <cstdint>
#include <map>

template<class T> class sparse_vectort
{
protected:
  typedef std::map<mp_integer, T> underlyingt;
  typedef typename underlyingt::key_type key_type;
  underlyingt underlying;
  mp_integer _size;

public:
  sparse_vectort() :
    _size(0) {}

  const T &operator[](const key_type &idx) const
  {
    INVARIANT(idx<_size, "index out of range");
    return underlying[idx];
  }

  T &operator[](const key_type &idx)
  {
    INVARIANT(idx<_size, "index out of range");
    return underlying[idx];
  }

  mp_integer size() const
  {
    return _size;
  }

  void resize(mp_integer new_size)
  {
    INVARIANT(new_size>=_size, "sparse vector can't be shrunk (yet)");
    _size=std::move(new_size);
  }

  typedef typename underlyingt::iterator iteratort;
  typedef typename underlyingt::const_iterator const_iteratort;

  iteratort begin() { return underlying.begin(); }
  const_iteratort begin() const { return underlying.begin(); }

  iteratort end() { return underlying.end(); }
  const_iteratort end() const { return underlying.end(); }

  const_iteratort find(const mp_integer &idx) { return underlying.find(idx); }
};

#endif // CPROVER_UTIL_SPARSE_VECTOR_H
