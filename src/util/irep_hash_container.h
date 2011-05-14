/*******************************************************************\

Module: IREP Hash Container

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IREP_HASH_H
#define CPROVER_IREP_HASH_H

#include "numbering.h"
#include "irep.h"

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

  // replacing the following two hash-tables by
  // maps doesn't make much difference in performance
    
  typedef hash_numbering<packedt, vector_hash> numberingt;
  numberingt numbering;
  
  typedef hash_map_cont<const void *, unsigned> ptr_hasht;
  ptr_hasht ptr_hash;

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
