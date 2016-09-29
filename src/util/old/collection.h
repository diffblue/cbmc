/*******************************************************************\

Module: String Storage

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STRING_COLLECTION_H
#define CPROVER_STRING_COLLECTION_H

#include "string_hash.h"
#include "hash_cont.h"

template <class T, class hash_function>
class collection
{
public:
  typedef T valuet;

  typedef hash_map_cont<T, unsigned, hash_function> member_mapt;
  typedef std::vector<T> member_vectort;
  
  typedef typename member_mapt::const_iterator const_iterator;
  
  const_iterator begin() const
  {
    return member_map.begin();
  }

  const_iterator end() const
  {
    return member_map.end();
  }

  class membert
  {
  public:
    membert()
    {
    }
    
    friend bool operator < (const membert &a, const membert &b)
    {
      return a.nr<b.nr;
    }
    
    membert(unsigned _nr):nr(_nr)
    {
    }
    
    friend class collection;
    
    unsigned get_nr() const
    {
      return nr;
    }
  
  protected:
    unsigned nr;
  };
  
  membert member(const T &x)
  {
    std::pair<typename member_mapt::iterator, bool> result=
      member_map.insert(std::pair<T, unsigned>(x, member_vector.size()));
      
    if(result.second)
      member_vector.push_back(x);

    return membert(result.first->second);
  }
  
  const T &operator [] (const membert m) const
  {
    return member_vector[m.nr];
  }
  
  const membert operator [] (const T &x)
  {
    return member(x);
  }
  
  void clear()
  {
    member_map.clear();
    member_vector.clear();
  }

protected:
  member_mapt member_map;
  member_vectort member_vector;
};

template <class T>
class collection_set
{
public:
  typedef T collectiont;
  
  collection_set():collection(NULL)
  {
  }
  
  void insert(unsigned nr)
  {
    if(members.size()<nr) members.resize(nr, false);
    members[nr]=true;
  }
  
  bool is_member(unsigned nr) const
  {
    if(members.size()<nr) return members[nr];
    return false;
  }
  
  void insert(
    collectiont &_collection,
    const typename collectiont::valuet &x)
  {
    set_collection(_collection);
    insert(_collection[x].get_nr());
  }

  #if 0  
  void insert(
    collectiont &_collection,
    const collection_set &x)
  {
    set_collection(_collection);

    if(x.collection==NULL) return;
    
    for(unsigned i=0; i<x.members.size(); i++)
    {
      
    }
  }
  #endif
  
  bool is_member(
    const typename collectiont::valuet &x) const
  {
    if(collection==NULL) return false;
    return is_member((*collection)[x].get_nr());
  }
  
  bool empty() const
  {
    for(unsigned i=0; i<members.size(); i++)
      if(members[i]) return false;

    return true;
  }
  
  void clear()
  {
    collection=NULL;
    members.clear();
  }
  
  void swap(collection_set &x)
  {
    std::swap(collection, x.collection);
    members.swap(x.members);
  }
  
  void insert(
    collection_set &x)
  {
    
  }
  
protected:
  typedef std::vector<bool> memberst;
  memberst members;
  
  void set_collection(collectiont &_collection)
  {
    if(collection==NULL)
      collection=&_collection;
    else
      assert(collection==&_collection);
  }
  
  collectiont *collection;
};

typedef collection_set<collection<std::string, string_hash> > string_collection_set;

#endif
