/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_NUMBERING_H
#define CPROVER_UTIL_NUMBERING_H

#include <unordered_map>
#include <vector>

#include "invariant.h"
#include "optional.h"

/// \tparam keyt: The type of keys which will be numbered.
/// \tparam hasht: The type of hashing functor used to hash keys.
template <typename keyt, typename hasht = std::hash<keyt>>
class numberingt final
{
public:
  using number_type = std::size_t; // NOLINT
  using key_type = keyt;           // NOLINT

private:
  using data_typet = std::vector<key_type>; // NOLINT
  data_typet data_;
  std::unordered_map<keyt, number_type, hasht> numbers_;

public:
  using size_type = typename data_typet::size_type;           // NOLINT
  using iterator = typename data_typet::iterator;             // NOLINT
  using const_iterator = typename data_typet::const_iterator; // NOLINT

  number_type number(const key_type &a)
  {
    const auto result = numbers_.emplace(a, number_type(numbers_.size()));

    if(result.second) // inserted?
    {
      data_.emplace_back(a);
      INVARIANT(data_.size() == numbers_.size(), "vector sizes must match");
    }

    return (result.first)->second;
  }

  optionalt<number_type> get_number(const key_type &a) const
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

  size_type size() const
  {
    return data_.size();
  }

  const key_type &at(size_type t) const
  {
    return data_.at(t);
  }

  key_type &operator[](size_type t)
  {
    return data_[t];
  }
  const key_type &operator[](size_type t) const
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


#endif // CPROVER_UTIL_NUMBERING_H
