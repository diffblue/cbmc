/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXPANDING_VECTOR_H
#define CPROVER_EXPANDING_VECTOR_H

#include <vector>

template<typename T>
class expanding_vector:public std::vector<T>
{
public:
  inline T & operator[] (typename std::vector<T>::size_type n)
  {
    check_index(n);
    return subt::operator[](n);
  }
  
  inline const T & operator[] (typename std::vector<T>::size_type n) const
  {
    // hack-ish const cast
    const_cast<expanding_vector *>(this)->check_index(n);
    return subt::operator[](n);
  }

protected:  
  typedef std::vector<T> subt;

  // make the vector large enough to contain 'n'
  inline void check_index(typename std::vector<T>::size_type n)
  {
    if(n>=subt::size()) subt::resize(n+1);
  }
};

#endif
