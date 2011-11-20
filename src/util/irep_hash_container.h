/*******************************************************************\

Module: IREP Hash Container

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IREP_HASH_H
#define CPROVER_IREP_HASH_H

#include <vector>

#include "numbering.h"
#include "hash_cont.h"

class irept;

class irep_hash_container_baset
{
public:
  unsigned number(const irept &irep);
  
  irep_hash_container_baset(bool _full):full(_full)
  {
  }
  
  void clear()
  {
    numbering.clear();
  }
  
protected:
  // replacing the following two hash-tables by
  // std::maps doesn't make much difference in performance

  // this is the first level: address of the content
  
  struct pointer_hash
  {
    inline size_t operator()(const void *p) const
    {
      return (size_t)p;
    }
  };

  typedef hash_map_cont<const void *, unsigned, pointer_hash> ptr_hasht;
  ptr_hasht ptr_hash;

  // this is the second level: content
      
  typedef std::vector<unsigned> packedt;
  
  struct vector_hash
  {
    inline size_t operator()(const packedt &p) const
    {
      size_t result=p.size();
      for(unsigned i=0; i<p.size(); i++)
        result^=p[i]<<i;
      return result;
    }
  };

  typedef hash_numbering<packedt, vector_hash> numberingt;
  numberingt numbering;
  
  void pack(const irept &irep, packedt &);
  
  bool full;
};

// excludes comments
class irep_hash_containert:
  public irep_hash_container_baset
{
public:
  irep_hash_containert():irep_hash_container_baset(false)
  {
  } 
};

// includes comments
class irep_full_hash_containert:
  public irep_hash_container_baset
{
public:
  irep_full_hash_containert():irep_hash_container_baset(true)
  {
  }
};

#endif
