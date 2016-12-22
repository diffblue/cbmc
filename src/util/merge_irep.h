/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MERGE_IREP_H
#define CPROVER_UTIL_MERGE_IREP_H

#include <unordered_set>

#include "irep.h"

class merged_irept:public irept
{
public:
  inline bool operator==(const merged_irept &other) const
  {
    // We assume that both are in the same container,
    // which isn't checked.
    return data==other.data;
  }

  inline bool operator<(const merged_irept &other) const
  {
    // again, assumes that both are in the same container
    return ((std::size_t)data)<((std::size_t)other.data);
  }

  inline std::size_t hash() const { return (std::size_t)data; }

  // copy constructor: will only copy from other merged_irepts
  inline merged_irept(const merged_irept &_src):irept(_src)
  {
  }

protected:
  // more general one can only be used by merged_irepst
  inline explicit merged_irept(const irept &src):irept(src)
  {
  }

  friend class merged_irepst;
};

struct merged_irep_hash
{
  inline std::size_t operator()(const merged_irept &irep) const
  { return irep.hash(); }
};

// internal, don't use me
class to_be_merged_irept:public irept
{
public:
  bool operator==(const to_be_merged_irept &other) const;
  std::size_t hash() const;

protected:
  // can only be used by merged_irepst
  inline explicit to_be_merged_irept(const irept &src):irept(src)
  {
  }

  friend class merged_irepst;
};

struct to_be_merged_irep_hash
{
  inline std::size_t operator()(const to_be_merged_irept &irep) const
  { return irep.hash(); }
};

class merged_irepst
{
public:
  inline const merged_irept &operator()(const irept &src)
  {
    return merged(src);
  }

protected:
  typedef std::unordered_set<merged_irept, merged_irep_hash> merged_irep_storet;
  merged_irep_storet merged_irep_store;

  typedef std::unordered_set<to_be_merged_irept, to_be_merged_irep_hash>
    to_be_merged_irep_storet;
  to_be_merged_irep_storet to_be_merged_irep_store;

  const merged_irept &merged(const irept &);
};

// Warning: the below uses irep_hash, as opposed to irep_full_hash,
// i.e., any comments will be disregarded during merging. Use
// merge_full_irept if any comments are of importance.

class merge_irept
{
public:
  void operator()(irept &);

protected:
  typedef std::unordered_set<irept, irep_hash> irep_storet;
  irep_storet irep_store;

  const irept & merged(const irept &irep);
};

class merge_full_irept
{
public:
  void operator()(irept &);

protected:
  typedef std::unordered_set<irept, irep_full_hash, irep_full_eq> irep_storet;
  irep_storet irep_store;

  const irept& merged(const irept &irep);
};

#endif // CPROVER_UTIL_MERGE_IREP_H
