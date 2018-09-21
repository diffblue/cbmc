// Copyright 2018 Diffblue Limited.

/// \file
/// A wrapper for maps that gives read-write access to elements but without
/// allowing addition or removal of elements

#ifndef CPROVER_UTIL_FIXED_KEYS_MAP_WRAPPER_H
#define CPROVER_UTIL_FIXED_KEYS_MAP_WRAPPER_H

template <typename mapt>
class fixed_keys_map_wrappert
{
private:
  mapt &map;

public:
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::iterator iterator;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::const_iterator const_iterator;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::reverse_iterator reverse_iterator;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::const_reverse_iterator const_reverse_iterator;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::key_type key_type;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::mapped_type mapped_type;
  // NOLINTNEXTLINE(readability/identifiers) - should match STL
  typedef typename mapt::size_type size_type;

  explicit fixed_keys_map_wrappert(mapt &map) : map(map)
  {
  }

  iterator begin()
  {
    return map.begin();
  }
  const_iterator begin() const
  {
    return map.begin();
  }
  iterator end()
  {
    return map.end();
  }
  const_iterator end() const
  {
    return map.end();
  }
  reverse_iterator rbegin()
  {
    return map.rbegin();
  }
  const_reverse_iterator rbegin() const
  {
    return map.rbegin();
  }
  reverse_iterator rend()
  {
    return map.rend();
  }
  const_reverse_iterator rend() const
  {
    return map.rend();
  }
  const_iterator cbegin() const
  {
    return map.begin();
  }
  const_iterator cend() const
  {
    return map.end();
  }
  const_reverse_iterator crbegin() const
  {
    return map.rbegin();
  }
  const_reverse_iterator crend() const
  {
    return map.rend();
  }

  bool empty() const
  {
    return map.empty();
  }
  size_type size() const
  {
    return map.size();
  }
  size_type count(const key_type &key) const
  {
    return map.count(key);
  }

  const mapped_type &at(const key_type &key) const
  {
    return map.at(key);
  }
  mapped_type &at(const key_type &key)
  {
    return map.at(key);
  }

  iterator find(const key_type &key)
  {
    return map.find(key);
  }
  const_iterator find(const key_type &key) const
  {
    return map.find(key);
  }
};

#endif // CPROVER_UTIL_FIXED_KEYS_MAP_WRAPPER_H
