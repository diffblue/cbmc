/*******************************************************************\

Module: Sorted-vector map

Author: Kiro

\*******************************************************************/

/// \file
/// A map with std::map's ordered-iteration and lookup interface, stored as a
/// sorted vector of pairs.  Lookup is O(log n), insertion and erasure O(n),
/// and -- the reason for it -- copying is ONE allocation instead of one per
/// entry.  For a map that is small-to-medium, rarely mutated and often copied
/// (the C++ front end's template maps are copied on every save/restore around
/// an instantiation) that is the dominant cost.

#ifndef CPROVER_UTIL_FLAT_MAP_H
#define CPROVER_UTIL_FLAT_MAP_H

#include <algorithm>
#include <utility>
#include <vector>

template <typename K, typename V, typename Compare = std::less<K>>
class flat_mapt
{
public:
  using key_type = K;
  using mapped_type = V;
  using value_type = std::pair<K, V>;
  using containert = std::vector<value_type>;
  using iterator = typename containert::iterator;
  using const_iterator = typename containert::const_iterator;
  using size_type = typename containert::size_type;

  iterator begin()
  {
    return entries.begin();
  }
  iterator end()
  {
    return entries.end();
  }
  const_iterator begin() const
  {
    return entries.begin();
  }
  const_iterator end() const
  {
    return entries.end();
  }
  bool empty() const
  {
    return entries.empty();
  }
  size_type size() const
  {
    return entries.size();
  }
  void clear()
  {
    entries.clear();
  }
  void swap(flat_mapt &other)
  {
    entries.swap(other.entries);
  }

  iterator find(const K &key)
  {
    auto it = lower_bound(key);
    return it != entries.end() && !compare(key, it->first) ? it : entries.end();
  }
  const_iterator find(const K &key) const
  {
    auto it = lower_bound(key);
    return it != entries.end() && !compare(key, it->first) ? it : entries.end();
  }
  size_type count(const K &key) const
  {
    return find(key) == entries.end() ? 0 : 1;
  }

  V &operator[](const K &key)
  {
    auto it = lower_bound(key);
    if(it == entries.end() || compare(key, it->first))
      it = entries.insert(it, value_type{key, V{}});
    return it->second;
  }

  std::pair<iterator, bool> insert(const value_type &value)
  {
    auto it = lower_bound(value.first);
    if(it != entries.end() && !compare(value.first, it->first))
      return {it, false};
    return {entries.insert(it, value), true};
  }
  template <typename... Args>
  std::pair<iterator, bool> emplace(const K &key, Args &&...args)
  {
    auto it = lower_bound(key);
    if(it != entries.end() && !compare(key, it->first))
      return {it, false};
    return {entries.emplace(it, key, V(std::forward<Args>(args)...)), true};
  }

  iterator erase(const_iterator pos)
  {
    return entries.erase(pos);
  }
  size_type erase(const K &key)
  {
    auto it = find(key);
    if(it == entries.end())
      return 0;
    entries.erase(it);
    return 1;
  }

  bool operator==(const flat_mapt &other) const
  {
    return entries == other.entries;
  }

private:
  containert entries;
  Compare compare;

  iterator lower_bound(const K &key)
  {
    return std::lower_bound(
      entries.begin(),
      entries.end(),
      key,
      [this](const value_type &entry, const K &k)
      { return compare(entry.first, k); });
  }
  const_iterator lower_bound(const K &key) const
  {
    return std::lower_bound(
      entries.begin(),
      entries.end(),
      key,
      [this](const value_type &entry, const K &k)
      { return compare(entry.first, k); });
  }
};

#endif // CPROVER_UTIL_FLAT_MAP_H
