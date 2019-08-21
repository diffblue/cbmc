/*******************************************************************\

Module: Dense integer map

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Dense integer map

#ifndef CPROVER_UTIL_DENSE_INTEGER_MAP_H
#define CPROVER_UTIL_DENSE_INTEGER_MAP_H

#include <limits>
#include <unordered_set>
#include <vector>

#include <util/invariant.h>

/// Identity functor. When we use C++20 this can be replaced with std::identity.
template <typename T>
class identity_functort
{
public:
  constexpr T &&operator()(T &&t) const
  {
    return std::forward<T>(t);
  }
};

/// A map type that is backed by a vector, which relies on the ability to (a)
/// see the keys that might be used in advance of their usage, and (b) map those
/// keys onto a dense range of integers. You should specialise
/// key_to_dense_integer for your key type before using. If it maps your keys
/// onto too sparse a range, considerable memory will be wasted.
///
/// The type is optimised for fast lookups at the expense of flexibility.
/// So far I've only implemented the support needed for use in
/// cfg_basic_blockst. Due to the vector storage the precise interface of
/// std::map is hard to achieve, but something close is practically achievable
/// for the interested developer.
template <class K, class V, class KeyToDenseInteger = identity_functort<K>>
class dense_integer_mapt
{
public:
  typedef std::vector<K> possible_keyst;

private:
  std::size_t offset;
  typedef std::vector<V> backing_storet;
  std::vector<V> map;
  std::vector<bool> value_set;
  std::size_t n_values_set;
  possible_keyst possible_keys_vector;

  std::size_t key_to_index(const K &key) const
  {
    std::size_t key_integer = KeyToDenseInteger{}(key);
    INVARIANT(key_integer >= offset, "index should be in range");
    return key_integer - offset;
  }

  void mark_index_set(std::size_t index)
  {
    if(!value_set[index])
    {
      ++n_values_set;
      value_set[index] = true;
    }
  }

public:
  dense_integer_mapt() : offset(0), n_values_set(0)
  {
  }

  template <typename Iter>
  void setup_for_keys(Iter first, Iter last)
  {
    std::size_t highest_key = std::numeric_limits<std::size_t>::min();
    std::size_t lowest_key = std::numeric_limits<std::size_t>::max();
    std::unordered_set<std::size_t> seen_keys;
    for(Iter it = first; it != last; ++it)
    {
      std::size_t integer_key = KeyToDenseInteger{}(*it);
      highest_key = std::max(integer_key, highest_key);
      lowest_key = std::min(integer_key, lowest_key);
      INVARIANT(
        seen_keys.insert(integer_key).second,
        "keys for use in dense_integer_mapt must be unique");
    }

    if(highest_key < lowest_key)
    {
      offset = 0;
    }
    else
    {
      offset = lowest_key;
      map.resize((highest_key - lowest_key) + 1);
      value_set.resize((highest_key - lowest_key) + 1);
    }

    possible_keys_vector.insert(possible_keys_vector.end(), first, last);
  }

  const V &at(const K &key) const
  {
    std::size_t index = key_to_index(key);
    INVARIANT(value_set[index], "map value should be set");
    return map.at(index);
  }
  V &at(const K &key)
  {
    std::size_t index = key_to_index(key);
    INVARIANT(value_set[index], "map value should be set");
    return map.at(index);
  }

  const V &operator[](const K &key) const
  {
    std::size_t index = key_to_index(key);
    mark_index_set(index);
    return map.at(index);
  }
  V &operator[](const K &key)
  {
    std::size_t index = key_to_index(key);
    mark_index_set(index);
    return map.at(index);
  }

  bool insert(const std::pair<const K, const V> &pair)
  {
    std::size_t index = key_to_index(pair.first);
    if(value_set[index])
      return false;
    mark_index_set(index);
    map.at(index) = pair.second;
    return true;
  }

  std::size_t count(const K &key) const
  {
    return value_set[key_to_index(key)];
  }

  std::size_t size() const
  {
    return n_values_set;
  }

  const possible_keyst &possible_keys() const
  {
    return possible_keys_vector;
  }
};

#endif // CPROVER_UTIL_DENSE_INTEGER_MAP_H
