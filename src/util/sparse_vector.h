/*******************************************************************\

Module: Sparse Vectors

Author: Romain Brenguier

\*******************************************************************/

/// \file
/// Sparse Vectors

#ifndef CPROVER_UTIL_SPARSE_VECTOR_H
#define CPROVER_UTIL_SPARSE_VECTOR_H

#include "invariant.h"

#include <cstdint>
#include <map>

template<class T> class sparse_vectort
{
protected:
  typedef std::map<uint64_t, T> underlyingt;
  underlyingt underlying;
  uint64_t _size;

public:
  sparse_vectort() :
    _size(0) {}

  const T &operator[](uint64_t idx) const
  {
    INVARIANT(idx<_size, "index out of range");
    return underlying[idx];
  }

  T &operator[](uint64_t idx)
  {
    INVARIANT(idx<_size, "index out of range");
    return underlying[idx];
  }

  uint64_t size() const
  {
    return _size;
  }

  void resize(uint64_t new_size)
  {
    INVARIANT(new_size>=_size, "sparse vector can't be shrunk (yet)");
    _size=new_size;
  }

  void clear()
  {
    underlying.clear();
    _size = 0;
  }

  typedef typename underlyingt::iterator iteratort;
  typedef typename underlyingt::const_iterator const_iteratort;

  iteratort begin() { return underlying.begin(); }
  const_iteratort begin() const { return underlying.begin(); }

  iteratort end() { return underlying.end(); }
  const_iteratort end() const { return underlying.end(); }

  const_iteratort find(uint64_t idx) { return underlying.find(idx); }
};

#endif // CPROVER_UTIL_SPARSE_VECTOR_H
