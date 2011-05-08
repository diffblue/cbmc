/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UNION_FIND_H
#define CPROVER_UNION_FIND_H

#include <assert.h>

#include <vector>

#include "numbering.h"

class unsigned_union_find
{
public:
  void make_union(unsigned a, unsigned b);
  unsigned find(unsigned a) const;  

  void intersection(const unsigned_union_find &other);

  // remove from any sets
  void isolate(unsigned a);

  void swap(unsigned_union_find &other)
  {
    other.nodes.swap(nodes);
  }

  void resize(unsigned size)
  {
    // only enlarge
    assert(nodes.size()<=size);
    nodes.resize(size);
  }
  
  void clear()
  {
    nodes.clear();
  }
  
  bool is_root(unsigned a) const
  {
    if(a>=size()) return true;
    return nodes[a].root;
  }
  
  bool same_set(unsigned a, unsigned b) const
  {
    return find(a)==find(b);
  }
  
  unsigned size() const
  {
    return nodes.size();
  }
  
  unsigned count(unsigned a) const
  {
    if(a>=size()) return 1;
    return nodes[find(a)].count;
  }
  
  void check_index(unsigned a)
  {
    if(a>=size()) resize(a+1);
  }
  
  unsigned count_roots() const
  {
    unsigned c=0;
    for(unsigned i=0; i<nodes.size(); i++)
      if(nodes[i].root) c++;
    return c;
  }
  
  void re_root(unsigned old, unsigned new_root);
  
  unsigned get_other(unsigned a);
  
protected:  
  struct nodet
  {
    // these two could be shared
    unsigned count;
    unsigned parent;

    bool root;
    
    nodet():count(1), parent(0), root(true)
    {
    }
  };

  std::vector<nodet> nodes;
};

template <typename T>
class union_find:public numbering<T>
{
public:
  // true == already in same set
  bool make_union(const T &a, const T &b)
  {
    unsigned na=number(a), nb=number(b);
    bool is_union=find_number(na)==find_number(nb);
    uuf.make_union(na, nb);
    return is_union;
  }
  
  const T &find(const T &a)
  {
    return find(number(a));
  }
  
  unsigned find_number(unsigned a) const
  {
    return uuf.find(a);
  }

  unsigned find_number(const T &a)
  {
    return uuf.find(number(a));
  }
  
  bool is_root_number(unsigned a) const
  {
    return uuf.is_root(a);
  }

  bool is_root(const T &a)
  {
    return is_root(number(a));
  }

  unsigned number(const T &a)
  {
    unsigned n=subt::number(a);
  
    if(n>=uuf.size())
      uuf.resize(this->size());
    
    assert(uuf.size()==this->size());
    
    return n;
  }
  
protected:
  unsigned_union_find uuf;
  typedef numbering<T> subt;
};

#endif
