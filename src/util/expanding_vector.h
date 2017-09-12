/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_EXPANDING_VECTOR_H
#define CPROVER_UTIL_EXPANDING_VECTOR_H

#include <vector>

template<typename T>
class expanding_vectort
{
  typedef std::vector<T> data_typet;
  data_typet data;

public:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::size_type size_type;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::const_iterator const_iterator;

  T &operator[] (typename std::vector<T>::size_type n)
  {
    if(n>=data.size())
      data.resize(n+1);
    return data[n];
  }

  void clear() { data.clear(); }

  iterator begin() { return data.begin(); }
  const_iterator begin() const { return data.begin(); }
  const_iterator cbegin() const { return data.cbegin(); }

  iterator end() { return data.end(); }
  const_iterator end() const { return data.end(); }
  const_iterator cend() const { return data.cend(); }

  size_type size() const { return data.size(); }

  void push_back(const T &t) { data.push_back(t); }
  void push_back(T &&t) { data.push_back(std::move(t)); }
};

#endif // CPROVER_UTIL_EXPANDING_VECTOR_H
