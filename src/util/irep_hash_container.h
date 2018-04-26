/*******************************************************************\

Module: IREP Hash Container

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// IREP Hash Container

#ifndef CPROVER_UTIL_IREP_HASH_CONTAINER_H
#define CPROVER_UTIL_IREP_HASH_CONTAINER_H

#include <vector>

#include "numbering.h"

class irept;

class irep_hash_container_baset
{
public:
  std::size_t number(const irept &irep);

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
    std::size_t operator()(const void *p) const
    {
      return (std::size_t)p;
    }
  };

  typedef std::unordered_map<const void *, std::size_t, pointer_hasht>
    ptr_hasht;
  ptr_hasht ptr_hash;

  // this is the second level: content

  typedef std::vector<std::size_t> packedt;

  struct vector_hasht
  {
    std::size_t operator()(const packedt &p) const;
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
