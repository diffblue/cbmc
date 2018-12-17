/*******************************************************************\

Module: Range

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Ranges: pair of begin and end iterators, which can be initialized from
/// containers, provide useful methods such as map, filter and concat which only
/// manipulate iterators, and can be used with ranged-for.

#ifndef CPROVER_UTIL_RANGE_H
#define CPROVER_UTIL_RANGE_H

#include <functional>
#include <type_traits>

#include <util/invariant.h>
#include <util/make_unique.h>

/// Iterator which applies some given function \c f after each increment and
/// returns its result on dereference.
template <typename iteratort, typename outputt>
class map_iteratort
{
public:
  using difference_type = typename iteratort::difference_type;
  using value_type = outputt;
  using pointer = const outputt *;
  using reference = const outputt &;
  using iterator_category = std::forward_iterator_tag;

  bool operator==(const map_iteratort &other) const
  {
    return underlying == other.underlying;
  }

  bool operator!=(const map_iteratort &other) const
  {
    return !(this->underlying == other.underlying);
  }

  /// Preincrement operator
  map_iteratort &operator++()
  {
    PRECONDITION(underlying != underlying_end);
    ++underlying;
    if(underlying != underlying_end)
      current = std::make_shared<outputt>((*f)(*underlying));
    return *this;
  }

  /// Postincrement operator
  const map_iteratort operator++(int)
  {
    map_iteratort tmp(*this);
    this->operator++();
    return tmp;
  }

  value_type &operator*()
  {
    return *current.get();
  }

  value_type *operator->()
  {
    return &(*current.get());
  }

  const value_type &operator*() const
  {
    return *current.get();
  }

  const value_type *operator->() const
  {
    return &(*current.get());
  }

  explicit map_iteratort(
    iteratort underlying,
    iteratort underlying_end,
    std::shared_ptr<
      std::function<value_type(const typename iteratort::value_type &)>> f)
    : underlying(std::move(underlying)),
      underlying_end(std::move(underlying_end)),
      f(std::move(f))
  {
    if(this->underlying != this->underlying_end)
      current = std::make_shared<outputt>((*this->f)(*this->underlying));
  }

private:
  iteratort underlying;
  iteratort underlying_end;
  std::shared_ptr<
    std::function<value_type(const typename iteratort::value_type &)>>
    f;

  /// Stores the result of \c f at the current position of the iterator.
  /// Equals nullptr if the iterator reached \c underlying_end.
  std::shared_ptr<outputt> current = nullptr;
};

/// Iterator which only stops at elements for which some given function \c f is
/// true.
template <typename iteratort>
class filter_iteratort
{
public:
  using difference_type = typename iteratort::difference_type;
  using value_type = typename iteratort::value_type;
  using pointer = const value_type *;
  using reference = const value_type &;
  using iterator_category = std::forward_iterator_tag;

  bool operator==(const filter_iteratort &other) const
  {
    return underlying == other.underlying;
  }

  bool operator!=(const filter_iteratort &other) const
  {
    return !(this->underlying == other.underlying);
  }

  /// Preincrement operator
  filter_iteratort &operator++()
  {
    ++underlying;
    point_to_first_to_peek();
    return *this;
  }

  /// Postincrement operator
  const filter_iteratort operator++(int)
  {
    filter_iteratort tmp(*this);
    this->operator++();
    return tmp;
  }

  value_type &operator*()
  {
    return *underlying;
  }

  value_type *operator->()
  {
    return &(*underlying);
  }

  const value_type &operator*() const
  {
    return *underlying;
  }

  const value_type *operator->() const
  {
    return &(*underlying);
  }

  /// Filter between \p underlying and \p end using \p f.
  /// If \c f is not true for any element between \p underlying and \p end, the
  /// constructed iterator is equal to the one which would have been constructed
  /// using
  /// ```
  /// filter_iteratort(f, end, end)
  /// ```
  filter_iteratort(
    std::shared_ptr<std::function<bool(const value_type &)>> f,
    iteratort underlying,
    iteratort end)
    : underlying(std::move(underlying)),
      underlying_end(std::move(end)),
      f(std::move(f))
  {
    point_to_first_to_peek();
  }

private:
  iteratort underlying;
  const iteratort underlying_end;
  std::shared_ptr<std::function<bool(const value_type &)>> f;

  /// Ensure that the underlying iterator is always positioned on an element
  /// for which `f` is true.
  /// This does nothing if \c f is satisfied at the current position.
  /// If \c f is not true for any element between underlying and underlying_end
  /// underlying will be incremented until underlying_end is reached.
  void point_to_first_to_peek()
  {
    while(underlying != underlying_end && !(*f)(*underlying))
      ++underlying;
  }
};

/// On increment, increments a first iterator and when the corresponding end
/// iterator is reached, starts to increment a second one.
/// Dereference corresponds to dereference on the first iterator if the end is
/// not reached yet, and on the second one otherwise.
template <typename first_iteratort, typename second_iteratort>
struct concat_iteratort
{
public:
  using difference_type = typename first_iteratort::difference_type;
  using value_type = typename first_iteratort::value_type;
  using pointer = const value_type *;
  using reference = const value_type &;
  using iterator_category = std::forward_iterator_tag;

  static_assert(
    std::is_same<value_type, typename first_iteratort::value_type>::value,
    "Concatenated iterators should have the same value type");

  bool operator==(const concat_iteratort &other) const
  {
    return first_begin == other.first_begin && first_end == other.first_end &&
           second_begin == other.second_begin;
  }

  bool operator!=(const concat_iteratort &other) const
  {
    return !(*this == other);
  }

  /// Preincrement operator
  concat_iteratort &operator++()
  {
    if(first_begin == first_end)
      ++second_begin;
    else
      ++first_begin;
    return *this;
  }

  /// Postincrement operator
  const concat_iteratort operator++(int)
  {
    concat_iteratort tmp(first_begin, first_end, second_begin);
    this->operator++();
    return tmp;
  }

  value_type &operator*()
  {
    if(first_begin == first_end)
      return *second_begin;
    return *first_begin;
  }

  value_type *operator->()
  {
    if(first_begin == first_end)
      return &(*second_begin);
    return &(*first_begin);
  }

  const value_type &operator*() const
  {
    if(first_begin == first_end)
      return *second_begin;
    return *first_begin;
  }

  const value_type *operator->() const
  {
    if(first_begin == first_end)
      return &(*second_begin);
    return &(*first_begin);
  }

  concat_iteratort(
    first_iteratort first_begin,
    first_iteratort first_end,
    second_iteratort second_begin)
    : first_begin(std::move(first_begin)),
      first_end(std::move(first_end)),
      second_begin(std::move(second_begin))
  {
  }

private:
  first_iteratort first_begin;
  first_iteratort first_end;
  second_iteratort second_begin;
};

/// A range is a pair of a begin and an end iterators.
/// The class provides useful methods such as map, filter and concat which only
/// manipulate iterators and thus don't have to create instances of heavy data
/// structures and avoid copies.
/// For instance, to iterate over two vectors, instead of writing
///
///     std::vector new_vector;
///     std::copy(v1.begin(), v1.end(), std::back_inserter(new_vector));
///     std::copy(v2.begin(), v2.end(), std::back_inserter(new_vector));
///     for(const auto &a : new_vector) {...}
///
/// It is possible to write:
///
///     auto range = make_range(v1).concat(make_range(v2));
///     for(const auto &a : range) {...}
///
/// Which is clearer and has the advantage of avoiding the creation of the
/// intermediary vector and the potentially expensive copies.
template <typename iteratort>
struct ranget final
{
public:
  using value_typet = typename iteratort::value_type;

  ranget(iteratort begin, iteratort end) : begin_value(begin), end_value(end)
  {
  }

  ranget<filter_iteratort<iteratort>>
  filter(std::function<bool(const value_typet &)> f)
  {
    auto shared_f = std::make_shared<decltype(f)>(std::move(f));
    filter_iteratort<iteratort> filter_begin(shared_f, begin(), end());
    filter_iteratort<iteratort> filter_end(shared_f, end(), end());
    return ranget<filter_iteratort<iteratort>>(filter_begin, filter_end);
  }

  /// The type of elements contained in the resulting range is deduced from the
  /// return type of \p `f`.
  template <typename functiont>
  auto map(functiont &&f) -> ranget<map_iteratort<
    iteratort,
    typename std::result_of<functiont(value_typet)>::type>>
  {
    using outputt = typename std::result_of<functiont(value_typet)>::type;
    auto shared_f = std::make_shared<
      std::function<outputt(const typename iteratort::value_type &)>>(
      std::forward<functiont>(f));
    auto map_begin =
      map_iteratort<iteratort, outputt>(begin(), end(), shared_f);
    auto map_end = map_iteratort<iteratort, outputt>(end(), end(), shared_f);
    return ranget<map_iteratort<iteratort, outputt>>(
      std::move(map_begin), std::move(map_end));
  }

  template <typename other_iteratort>
  ranget<concat_iteratort<iteratort, other_iteratort>>
  concat(ranget<other_iteratort> other)
  {
    auto concat_begin = concat_iteratort<iteratort, other_iteratort>(
      begin(), end(), other.begin());
    auto concat_end =
      concat_iteratort<iteratort, other_iteratort>(end(), end(), other.end());
    return ranget<concat_iteratort<iteratort, other_iteratort>>(
      concat_begin, concat_end);
  }

  bool empty() const
  {
    return begin_value == end_value;
  }

  iteratort begin()
  {
    return begin_value;
  }

  const iteratort &end() const
  {
    return end_value;
  }

private:
  iteratort begin_value;
  iteratort end_value;
};

template <typename iteratort>
ranget<iteratort> make_range(iteratort begin, iteratort end)
{
  return ranget<iteratort>(begin, end);
}

template <typename containert>
auto make_range(containert &container) -> ranget<decltype(container.begin())>
{
  return ranget<decltype(container.begin())>(
    container.begin(), container.end());
}

#endif // CPROVER_UTIL_RANGE_H
