/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_NUMBERING_H
#define CPROVER_NUMBERING_H

#include <cassert>
#include <map>
#include <vector>
#include <climits>
#include <list>

#include "trie.h"
#include "hash_cont.h"

// trie stores lists of T
template <typename T>
class trie_numbering
{
public:
  typedef std::list<T> objectt;
  typedef unsigned number_type;

  number_type number(const objectt &a)
  {
    if(a.empty())
      return UINT_MAX-1;

    std::pair<bool, const numberst &> p=numbers.insert(a, objects.size());

    if(p.first) // inserted?
    {
      objects.push_back(&p.second);
      assert(objects.size()!=UINT_MAX);
      assert(objects.size()!=UINT_MAX-1);
    }

    return p.second.value;
  }

  inline number_type operator()(const objectt &a)
  {
    return number(a);
  }

  bool get_number(const objectt &a, number_type &n) const
  {
    if(a.empty())
    {
      n=UINT_MAX-1;
      return false;
    }

    unsigned m=numbers.find(a);
    if(m==UINT_MAX)
      return true;

    n=m;
    return false;
  }

  const objectt get_object(number_type n) const
  {
    objectt o;
    assert(o.empty());

    if(n==UINT_MAX-1)
      return o;

    objects.at(n)->build_word(o);
    return o;
  }

  void get_object(number_type n, objectt &o) const
  {
    assert(o.empty());

    if(n==UINT_MAX-1)
      return;

    objects.at(n)->build_word(o);
  }

  void clear()
  {
    numbers.clear();
    objects.clear();
  }

protected:
  typedef trie<T, number_type, UINT_MAX> numberst;
  numberst numbers;

  typedef std::vector<const numberst *> objectst;
  objectst objects;
};

// numbering that stores each object only once, uses iterator for
// second instance
template <typename T>
class numbering_one
{
public:
  typedef unsigned int number_type;

  number_type number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result=
      numbers.insert(
        std::pair<T, number_type>(a, number_type(numbers.size())));

    if(result.second) // inserted?
    {
      iterators.push_back(result.first);
      assert(iterators.size()==numbers.size());
    }

    return (result.first)->second;
  }

  inline number_type operator()(const T &a)
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

  const T &get_object(number_type n) const
  {
    return iterators.at(n)->first;
  }

  void clear()
  {
    numbers.clear();
    iterators.clear();
  }

protected:
  typedef std::map<T, number_type> numberst;
  numberst numbers;

  typedef std::vector<typename numberst::const_iterator> iteratorst;
  iteratorst iterators;
};

template <typename T>
class numbering:public std::vector<T>
{
public:
  typedef std::size_t number_type;

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
  
  inline number_type operator()(const T &a)
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
  typedef std::vector<T> subt;

  typedef std::map<T, number_type> numberst;
  numberst numbers;  
};

template <typename T, class hash_fkt>
class hash_numbering:public std::vector<T>
{
public:
  typedef unsigned int number_type;

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
  typedef std::vector<T> subt;

  typedef hash_map_cont<T, number_type, hash_fkt> numberst;
  numberst numbers;  
};

#endif
