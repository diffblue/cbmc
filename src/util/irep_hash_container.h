/*******************************************************************\

Module: IREP Hash Container

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_IREP_HASH_CONTAINER_H
#define CPROVER_UTIL_IREP_HASH_CONTAINER_H

#include <cstdlib>  // for size_t
#include <vector>

#include "irep_hash.h"
#include "numbering.h"

class irept;

class irep_hash_container_baset
{
public:
  size_t number(const irept &irep);

  explicit irep_hash_container_baset(bool _full):full(_full)
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

  struct pointer_hasht
  {
    inline size_t operator()(const void *p) const
    {
      return (size_t)p;
    }
  };

  typedef std::unordered_map<const void *, size_t, pointer_hasht>
    ptr_hasht;
  ptr_hasht ptr_hash;

  // this is the second level: content

  typedef std::vector<size_t> packedt;

  struct vector_hasht
  {
    inline size_t operator()(const packedt &p) const
    {
      size_t result=p.size(); // seed
      for(auto elem : p)
        result=hash_combine(result, elem);
      return result;
    }
  };

  typedef hash_numbering<packedt, vector_hasht> numberingt;
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

#endif // CPROVER_UTIL_IREP_HASH_CONTAINER_H
