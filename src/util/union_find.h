/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UNION_FIND_H
#define CPROVER_UNION_FIND_H

#include <cassert>
#include <vector>

#include "numbering.h"

// Standard union find with weighting and path compression.
// See http://www.cs.princeton.edu/~rs/AlgsDS07/01UnionFind.pdf

class unsigned_union_find
{
public:
  typedef std::size_t size_type;

protected:
  struct nodet
  {
    size_type count; // set size
    size_type parent;

    // constructs a root node
    explicit nodet(size_type index):count(1), parent(index)
    {
    }
  };

  // This is mutable to allow path compression in find().
  mutable std::vector<nodet> nodes;

public:
  // merge the sets 'a' and 'b'
  void make_union(size_type a, size_type b);

  // find the root of the set 'a' belongs to
  size_type find(size_type a) const;

  // Makes 'this' the union-find with the following:
  // any union in 'this' will be present in both source sets,
  // i.e., this is the strongest implication of the two
  // data structures.
  void intersection(const unsigned_union_find &other);

  // remove from any sets
  void isolate(size_type a);

  inline void swap(unsigned_union_find &other)
  {
    other.nodes.swap(nodes);
  }

  inline void resize(size_type size)
  {
    // We only enlarge. Shrinking is yet to be implemented.
    assert(nodes.size()<=size);
    nodes.reserve(size);
    while(nodes.size()<size)
      nodes.push_back(nodet(nodes.size()));
  }
  
  inline void clear()
  {
    nodes.clear();
  }

  // is 'a' a root?  
  inline bool is_root(size_type a) const
  {
    if(a>=size()) return true;
    // a root is its own parent
    return nodes[a].parent==a;
  }

  // are 'a' and 'b' in the same set?
  inline bool same_set(size_type a, size_type b) const
  {
    return find(a)==find(b);
  }

  // total number of elements  
  inline size_type size() const
  {
    return nodes.size();
  }

  // size of the set that 'a' is in  
  inline size_type count(size_type a) const
  {
    if(a>=size()) return 1;
    return nodes[find(a)].count;
  }

  // make the array large enough to contain 'a'  
  inline void check_index(size_type a)
  {
    if(a>=size()) resize(a+1);
  }

  // number of disjoint sets  
  size_type count_roots() const
  {
    size_type c=0;
    for(size_type i=0; i<nodes.size(); i++)
      if(is_root(i)) c++;
    return c;
  }

  // makes 'new_root' the root of the set 'old'  
  void re_root(size_type old, size_type new_root);

  // find a different member of the same set
  size_type get_other(size_type a);
};

template <typename T>
class union_find:public numbering<T>
{
public:
  typedef typename numbering<T>::size_type size_type;

  // true == already in same set
  bool make_union(const T &a, const T &b)
  {
    size_type na=number(a), nb=number(b);
    bool is_union=find_number(na)==find_number(nb);
    uuf.make_union(na, nb);
    return is_union;
  }
  
  // are 'a' and 'b' in the same set?
  inline bool same_set(const T &a, const T &b)
  {
    size_type na=number(a), nb=number(b);
    return uuf.same_set(na, nb);
  }

  inline const T &find(const T &a)
  {
    return find(number(a));
  }
  
  inline size_type find_number(size_type a) const
  {
    return uuf.find(a);
  }

  inline size_type find_number(const T &a)
  {
    return uuf.find(number(a));
  }
  
  inline bool is_root_number(size_type a) const
  {
    return uuf.is_root(a);
  }

  inline bool is_root(const T &a)
  {
    return is_root(number(a));
  }

  inline size_type number(const T &a)
  {
    size_type n=subt::number(a);
  
    if(n>=uuf.size())
      uuf.resize(this->size());
    
    assert(uuf.size()==this->size());
    
    return n;
  }

  inline void clear()
  {
    subt::clear();
    uuf.clear();
  }  

protected:
  unsigned_union_find uuf;
  typedef numbering<T> subt;
};

#endif
