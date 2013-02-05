/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_NUMBERING_H
#define CPROVER_NUMBERING_H

#include <cassert>
#include <map>
#include <vector>

#include "hash_cont.h"

template <typename T>
class numbering:public std::vector<T>
{
public:
  unsigned number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result=
      numbers.insert(
      std::pair<T, unsigned>
      (a, unsigned(numbers.size())));

    if(result.second) // inserted?
    {
      this->push_back(a);
      assert(this->size()==numbers.size());
    }
    
    return (result.first)->second;
  }
  
  bool get_number(const T &a, unsigned &n) const
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

  typedef std::map<T, unsigned> numberst;
  numberst numbers;  
};

template <typename T, class hash_fkt>
class hash_numbering:public std::vector<T>
{
public:
  unsigned number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result=
      numbers.insert(
      std::pair<T, unsigned>
      (a, unsigned(numbers.size())));

    if(result.second) // inserted?
    {
      this->push_back(a);
      assert(this->size()==numbers.size());
    }
    
    return (result.first)->second;
  }
  
  bool get_number(const T &a, unsigned &n) const
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

  typedef hash_map_cont<T, unsigned, hash_fkt> numberst;
  numberst numbers;  
};

#endif
