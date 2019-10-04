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
#include <util/optional.h>

/// Identity functor. When we use C++20 this can be replaced with std::identity.
class identity_functort
{
public:
  template <typename T>
  constexpr T &&operator()(T &&t) const
  {
    return std::forward<T>(t);
  }
};

/// A map type that is backed by a vector, which relies on the ability to (a)
/// see the keys that might be used in advance of their usage, and (b) map those
/// keys onto a dense range of integers. You should specialise
/// key_to_dense_integer for your key type before using. If it maps your keys
/// onto too sparse a range, considerable memory will be wasted, as well as time
/// spent skipping over the unused indices while iterating.
///
/// Value type V must be default constructible.
///
/// The type is optimised for fast lookups at the expense of flexibility.
/// It makes one compromise on the iterface of std::map / unordered_map: the
/// iterator refers to a pair<key, optionalt<value>>, where the value optional
/// will always be defined. This is because the backing store uses optionalt
/// this way and we don't want to impose the price of copying the key and value
/// each time we move the iterator just so we have a <const K, V> & to give out.
///
/// Undocumented functions with matching names have the same semantics as
/// std::map equivalents (including perfect iterator stability, with ordering
/// according to the given KeyToDenseInteger function)
template <class K, class V, class KeyToDenseInteger = identity_functort>
class dense_integer_mapt
{
public:
  /// Type of the container returned by \ref possible_keys
  typedef std::vector<K> possible_keyst;

private:
  // Offset between keys resulting from KeyToDenseInteger{}(key) and indices
  // into map.
  int64_t offset;

  typedef std::vector<std::pair<K, V>> backing_storet;

  // Main store: contains <key, value> pairs, where entries at positions with
  // no corresponding key are default-initialized and entries with a
  // corresponding key but no value set yet have the correct key but a default-
  // initialized value. Both of these are skipped by this type's iterators.
  backing_storet map;

  // Indicates whether a given position in \ref map's value has been set, and
  // therefore whether our iterators should stop at a given location. We use
  // this auxiliary structure rather than `pair<K, optionalt<V>>` in \ref map
  // because this way we can more easily return a std::map-like
  // std::pair<const K, V> & from the iterator.
  std::vector<bool> value_set;

  // Population count (number of '1's) in value_set, i.e., number of keys whose
  // values have been set.
  std::size_t n_values_set;

  // "Allowed" keys passed to \ref setup_for_keys. Attempting to use keys not
  // included in this vector may result in an invariant failure, but can
  // sometimes silently succeed
  possible_keyst possible_keys_vector;

  // Convert a key into an index into \ref map
  std::size_t key_to_index(const K &key) const
  {
    auto key_integer = KeyToDenseInteger{}(key);
    INVARIANT(((int64_t)key_integer) >= offset, "index should be in range");
    auto ret = (std::size_t)key_integer - (std::size_t)offset;
    INVARIANT(ret < map.size(), "index should be in range");
    return ret;
  }

  // Note that \ref map entry at offset \ref index has been set.
  void mark_index_set(std::size_t index)
  {
    if(!value_set[index])
    {
      ++n_values_set;
      value_set[index] = true;
    }
  }

  // Has the \ref map entry at offset \ref index been set?
  bool index_is_set(std::size_t index) const
  {
    return value_set[index];
  }

  // Support class used to implement both const and non-const iterators
  // This is just a std::vector iterator pointing into \ref map, but with an
  // operator++ that skips unset values.
  template <class UnderlyingIterator, class UnderlyingValue>
  class iterator_templatet
    : public std::iterator<std::forward_iterator_tag, UnderlyingValue>
  {
    // Type of the std::iterator support class we inherit
    typedef std::iterator<std::forward_iterator_tag, UnderlyingValue>
      base_typet;
    // Type of this template instantiation
    typedef iterator_templatet<UnderlyingIterator, UnderlyingValue> self_typet;
    // Type of our containing \ref dense_integer_mapt
    typedef dense_integer_mapt<K, V, KeyToDenseInteger> map_typet;

  public:
    iterator_templatet(UnderlyingIterator it, const map_typet &underlying_map)
      : underlying_iterator(it), underlying_map(underlying_map)
    {
      it = skip_unset_values(it);
    }

    /// Convert iterator to const_iterator
    /// (redundant when defined in the const_iterator itself)
    operator iterator_templatet<
      typename backing_storet::const_iterator,
      const typename backing_storet::value_type>() const
    {
      return {underlying_iterator, underlying_map};
    }

    self_typet operator++()
    {
      self_typet i = *this;
      underlying_iterator = advance(underlying_iterator);
      return i;
    }
    self_typet operator++(int junk)
    {
      underlying_iterator = advance(underlying_iterator);
      return *this;
    }
    typename base_typet::reference operator*() const
    {
      return *underlying_iterator;
    }
    typename base_typet::pointer operator->() const
    {
      return &*underlying_iterator;
    }
    bool operator==(const self_typet &rhs) const
    {
      return underlying_iterator == rhs.underlying_iterator;
    }
    bool operator!=(const self_typet &rhs) const
    {
      return underlying_iterator != rhs.underlying_iterator;
    }

  private:
    // Advance \ref it to the next map entry with an initialized value
    UnderlyingIterator advance(UnderlyingIterator it)
    {
      return skip_unset_values(std::next(it));
    }

    // Return the next iterator >= it with its value set
    UnderlyingIterator skip_unset_values(UnderlyingIterator it)
    {
      auto iterator_pos = (std::size_t)std::distance(
        underlying_map.map.begin(),
        (typename backing_storet::const_iterator)it);
      while((std::size_t)iterator_pos < underlying_map.map.size() &&
            !underlying_map.value_set.at(iterator_pos))
      {
        ++iterator_pos;
        ++it;
      }
      return it;
    }

    // Wrapped std::vector iterator
    UnderlyingIterator underlying_iterator;
    const map_typet &underlying_map;
  };

public:
  /// iterator. Stable with respect to all operations on this type once
  /// setup_for_keys has been called.
  typedef iterator_templatet<
    typename backing_storet::iterator,
    typename backing_storet::value_type>
    iterator;

  /// const iterator. Stable with respect to all operations on this type once
  /// setup_for_keys has been called.
  typedef iterator_templatet<
    typename backing_storet::const_iterator,
    const typename backing_storet::value_type>
    const_iterator;

  dense_integer_mapt() : offset(0), n_values_set(0)
  {
  }

  /// Set the keys that are allowed to be used in this container. Checks that
  /// the integers produced for each key by `KeyToDenseInteger` are unique
  /// and fall within a std::size_t's range (the integers are allowed to be
  /// negative so long as max(integers) - min(integers) <= max-size_t).
  /// This should be called before the container is used and not called again.
  /// Using keys not provided to this function with operator[], insert, at(...)
  /// etc may cause an invariant failure or undefined behaviour.
  template <typename Iter>
  void setup_for_keys(Iter first, Iter last)
  {
    INVARIANT(
      size() == 0,
      "setup_for_keys must only be called on a newly-constructed container");

    int64_t highest_key = std::numeric_limits<int64_t>::min();
    int64_t lowest_key = std::numeric_limits<int64_t>::max();
    std::unordered_set<int64_t> seen_keys;
    for(Iter it = first; it != last; ++it)
    {
      int64_t integer_key = (int64_t)KeyToDenseInteger{}(*it);
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
      std::size_t map_size = (std::size_t)((highest_key - lowest_key) + 1);
      INVARIANT(
        map_size > 0, // overflowed?
        "dense_integer_mapt size should fit in std::size_t");
      INVARIANT(
        map_size <= std::numeric_limits<std::size_t>::max(),
        "dense_integer_mapt size should fit in std::size_t");
      offset = lowest_key;
      map.resize(map_size);
      for(Iter it = first; it != last; ++it)
        map.at(key_to_index(*it)).first = *it;
      value_set.resize(map_size);
    }

    possible_keys_vector.insert(possible_keys_vector.end(), first, last);
  }

  const V &at(const K &key) const
  {
    std::size_t index = key_to_index(key);
    INVARIANT(index_is_set(index), "map value should be set");
    return map.at(index).second;
  }
  V &at(const K &key)
  {
    std::size_t index = key_to_index(key);
    INVARIANT(index_is_set(index), "map value should be set");
    return map.at(index).second;
  }

  V &operator[](const K &key)
  {
    std::size_t index = key_to_index(key);
    mark_index_set(index);
    return map.at(index).second;
  }

  std::pair<iterator, bool> insert(const std::pair<const K, V> &pair)
  {
    auto index = key_to_index(pair.first);
    auto signed_index =
      static_cast<typename backing_storet::iterator::difference_type>(index);
    iterator it{std::next(map.begin(), signed_index), *this};

    if(index_is_set(index))
      return {it, false};
    else
    {
      mark_index_set(index);
      map.at(index).second = pair.second;
      return {it, true};
    }
  }

  std::size_t count(const K &key) const
  {
    return index_is_set(key_to_index(key));
  }

  std::size_t size() const
  {
    return n_values_set;
  }

  const possible_keyst &possible_keys() const
  {
    return possible_keys_vector;
  }

  iterator begin()
  {
    return iterator{map.begin(), *this};
  }

  iterator end()
  {
    return iterator{map.end(), *this};
  }

  const_iterator begin() const
  {
    return const_iterator{map.begin(), *this};
  }

  const_iterator end() const
  {
    return const_iterator{map.end(), *this};
  }

  const_iterator cbegin() const
  {
    return begin();
  }

  const_iterator cend() const
  {
    return end();
  }
};

#endif // CPROVER_UTIL_DENSE_INTEGER_MAP_H
