/*******************************************************************\

Module: IREP Hash Container

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// IREP Hash Container

#ifndef CPROVER_UTIL_IREP_HASH_CONTAINER_H
#define CPROVER_UTIL_IREP_HASH_CONTAINER_H

#include <vector>

#include "irep.h"
#include "numbering.h"

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

  struct irep_entryt
  {
    std::size_t number;
    irept irep; // copy to keep addresses stable

    irep_entryt(std::size_t _number, const irept &_irep)
      : number(_number), irep(_irep)
    {
    }
  };

  typedef std::unordered_map<const void *, irep_entryt, pointer_hasht>
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

template <typename Key, typename T>
class irep_hash_mapt
{
protected:
  using mapt = std::map<std::size_t, T>;

public:
  using key_type = Key;
  using mapped_type = T;
  using value_type = std::pair<const Key, T>;
  using const_iterator = typename mapt::const_iterator;
  using iterator = typename mapt::iterator;

  const_iterator find(const Key &key) const
  {
    return map.find(hash_container.number(key));
  }

  iterator find(const Key &key)
  {
    return map.find(hash_container.number(key));
  }

  const_iterator begin() const
  {
    return map.begin();
  }

  iterator begin()
  {
    return map.begin();
  }

  const_iterator end() const
  {
    return map.end();
  }

  iterator end()
  {
    return map.end();
  }

  void clear()
  {
    hash_container.clear();
    map.clear();
  }

  std::size_t size() const
  {
    return map.size();
  }

  bool empty() const
  {
    return map.empty();
  }

  T &operator[](const Key &key)
  {
    const std::size_t i = hash_container.number(key);
    return map[i];
  }

  std::pair<iterator, bool> insert(const value_type &value)
  {
    const std::size_t i = hash_container.number(value.first);
    return map.emplace(i, value.second);
  }

  void erase(iterator it)
  {
    map.erase(it);
  }

  void swap(irep_hash_mapt<Key, T> &other)
  {
    std::swap(hash_container, other.hash_container);
    std::swap(map, other.map);
  }

protected:
  mutable irep_hash_containert hash_container;
  mapt map;
};

#endif // CPROVER_UTIL_IREP_HASH_CONTAINER_H
