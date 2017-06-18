/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_EXPANDING_VECTOR_H
#define CPROVER_UTIL_EXPANDING_VECTOR_H

#include <vector>

template<typename T>
class expanding_vectort:public std::vector<T>
{
public:
  T &operator[] (typename std::vector<T>::size_type n)
  {
    check_index(n);
    return subt::operator[](n);
  }

  const T &operator[] (typename std::vector<T>::size_type n) const
  {
    // hack-ish const cast
    const_cast<expanding_vectort*>(this)->check_index(n);
    return subt::operator[](n);
  }

protected:
  using subt = std::vector<T>;

  // make the vector large enough to contain 'n'
  void check_index(typename std::vector<T>::size_type n)
  {
    if(n>=subt::size())
      subt::resize(n+1);
  }
};

#endif // CPROVER_UTIL_EXPANDING_VECTOR_H
