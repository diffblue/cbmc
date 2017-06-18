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


template <typename T>
// NOLINTNEXTLINE(readability/identifiers)
class numbering:public std::vector<T>
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  using number_type = std::size_t;

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
    subt::clear();
    numbers.clear();
  }

protected:
  using subt = std::vector<T>;

  typedef std::map<T, number_type> numberst;
  numberst numbers;
};

template <typename T, class hash_fkt>
// NOLINTNEXTLINE(readability/identifiers)
class hash_numbering:public std::vector<T>
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  using number_type = unsigned int;

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
    subt::clear();
    numbers.clear();
  }

protected:
  using subt = std::vector<T>;

  typedef std::unordered_map<T, number_type, hash_fkt> numberst;
  numberst numbers;
};

#endif // CPROVER_UTIL_NUMBERING_H
