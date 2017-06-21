/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_NUMBERING_H
#define CPROVER_UTIL_NUMBERING_H

#include <cassert>
#include <map>
#include <unordered_map>
#include <vector>

#include <util/invariant.h>

template <typename T>
// NOLINTNEXTLINE(readability/identifiers)
class numbering final
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef std::size_t number_type;

private:
  typedef std::vector<T> data_typet;
  data_typet data;
  typedef std::map<T, number_type> numberst;
  numberst numbers;

public:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::size_type size_type;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::const_iterator const_iterator;

  number_type number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result=
      numbers.insert(
      std::pair<T, number_type>
      (a, number_type(numbers.size())));

    if(result.second) // inserted?
    {
      data.push_back(a);
      INVARIANT(data.size()==numbers.size(), "vector sizes must match");
    }

    return (result.first)->second;
  }

  number_type operator()(const T &a)
  {
    return number(a);
  }

  bool get_number(const T &a, number_type &n) const
  {
    typename numberst::const_iterator it=numbers.find(a);

    if(it==numbers.end())
      return true;

    n=it->second;
    return false;
  }

  void clear()
  {
    data.clear();
    numbers.clear();
  }

  size_t size() const { return data.size(); }

  T &operator[](size_type t) { return data[t]; }
  const T &operator[](size_type t) const { return data[t]; }

  iterator begin() { return data.begin(); }
  const_iterator begin() const { return data.begin(); }
  const_iterator cbegin() const { return data.cbegin(); }

  iterator end() { return data.end(); }
  const_iterator end() const { return data.end(); }
  const_iterator cend() const { return data.cend(); }
};

template <typename T, class hash_fkt>
// NOLINTNEXTLINE(readability/identifiers)
class hash_numbering final
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef unsigned int number_type;

private:
  typedef std::vector<T> data_typet;
  data_typet data;
  typedef std::unordered_map<T, number_type, hash_fkt> numberst;
  numberst numbers;

public:
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::size_type size_type;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename data_typet::const_iterator const_iterator;

  number_type number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result=
      numbers.insert(
      std::pair<T, number_type>
      (a, number_type(numbers.size())));

    if(result.second) // inserted?
    {
      this->push_back(a);
      assert(this->size()==numbers.size());
    }

    return (result.first)->second;
  }

  bool get_number(const T &a, number_type &n) const
  {
    typename numberst::const_iterator it=numbers.find(a);

    if(it==numbers.end())
      return true;

    n=it->second;
    return false;
  }

  void clear()
  {
    data.clear();
    numbers.clear();
  }

  template <typename U>
  void push_back(U &&u) { data.push_back(std::forward<U>(u)); }

  T &operator[](size_type t) { return data[t]; }
  const T &operator[](size_type t) const { return data[t]; }

  size_type size() const { return data.size(); }

  iterator begin() { return data.begin(); }
  const_iterator begin() const { return data.begin(); }
  const_iterator cbegin() const { return data.cbegin(); }

  iterator end() { return data.end(); }
  const_iterator end() const { return data.end(); }
  const_iterator cend() const { return data.cend(); }
};

#endif // CPROVER_UTIL_NUMBERING_H
