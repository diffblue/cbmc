/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_NUMBERING_H
#define CPROVER_UTIL_NUMBERING_H

#include <cassert>
#include <map>
#include <unordered_map>
#include <vector>

#include <util/invariant.h>
#include <util/optional.h>

template <typename T>
// NOLINTNEXTLINE(readability/identifiers)
class numbering final
{
public:
  using number_type = std::size_t; // NOLINT

private:
  using data_typet = std::vector<T>; // NOLINT
  data_typet data_;
  using numberst = std::map<T, number_type>; // NOLINT
  numberst numbers_;

public:
  using size_type = typename data_typet::size_type;           // NOLINT
  using iterator = typename data_typet::iterator;             // NOLINT
  using const_iterator = typename data_typet::const_iterator; // NOLINT

  number_type number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result = numbers_.insert(
      std::pair<T, number_type>(a, number_type(numbers_.size())));

    if(result.second) // inserted?
    {
      data_.push_back(a);
      INVARIANT(data_.size() == numbers_.size(), "vector sizes must match");
    }

    return (result.first)->second;
  }

  optionalt<number_type> get_number(const T &a) const
  {
    const auto it = numbers_.find(a);
    if(it == numbers_.end())
    {
      return {};
    }
    return it->second;
  }

  void clear()
  {
    data_.clear();
    numbers_.clear();
  }

  size_t size() const
  {
    return data_.size();
  }

  T &operator[](size_type t)
  {
    return data_[t];
  }
  const T &operator[](size_type t) const
  {
    return data_[t];
  }

  iterator begin()
  {
    return data_.begin();
  }
  const_iterator begin() const
  {
    return data_.begin();
  }
  const_iterator cbegin() const
  {
    return data_.cbegin();
  }

  iterator end()
  {
    return data_.end();
  }
  const_iterator end() const
  {
    return data_.end();
  }
  const_iterator cend() const
  {
    return data_.cend();
  }
};

template <typename T, class hash_fkt>
// NOLINTNEXTLINE(readability/identifiers)
class hash_numbering final
{
public:
  using number_type = unsigned int; // NOLINT

private:
  using data_typet = std::vector<T>; // NOLINT
  data_typet data_;
  using numberst = std::unordered_map<T, number_type, hash_fkt>; // NOLINT
  numberst numbers_;

public:
  using size_type = typename data_typet::size_type;           // NOLINT
  using iterator = typename data_typet::iterator;             // NOLINT
  using const_iterator = typename data_typet::const_iterator; // NOLINT

  number_type number(const T &a)
  {
    std::pair<typename numberst::const_iterator, bool> result = numbers_.insert(
      std::pair<T, number_type>(a, number_type(numbers_.size())));

    if(result.second) // inserted?
    {
      this->push_back(a);
      assert(this->size() == numbers_.size());
    }

    return (result.first)->second;
  }

  optionalt<number_type> get_number(const T &a) const
  {
    const auto it = numbers_.find(a);

    if(it == numbers_.end())
    {
      return {};
    }
    return it->second;
  }

  void clear()
  {
    data_.clear();
    numbers_.clear();
  }

  template <typename U>
  void push_back(U &&u)
  {
    data_.push_back(std::forward<U>(u));
  }

  T &operator[](size_type t)
  {
    return data_[t];
  }
  const T &operator[](size_type t) const
  {
    return data_[t];
  }

  T &at(size_type t)
  {
    return data_.at(t);
  }
  const T &at(size_type t) const
  {
    return data_.at(t);
  }

  size_type size() const
  {
    return data_.size();
  }

  iterator begin()
  {
    return data_.begin();
  }
  const_iterator begin() const
  {
    return data_.begin();
  }
  const_iterator cbegin() const
  {
    return data_.cbegin();
  }

  iterator end()
  {
    return data_.end();
  }
  const_iterator end() const
  {
    return data_.end();
  }
  const_iterator cend() const
  {
    return data_.cend();
  }
};

#endif // CPROVER_UTIL_NUMBERING_H
