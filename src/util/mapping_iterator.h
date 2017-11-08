/*******************************************************************\

Module: Iterator utilities

Author: @reuk

\*******************************************************************/

#ifndef CPROVER_UTIL_MAPPING_ITERATOR_H
#define CPROVER_UTIL_MAPPING_ITERATOR_H

#include <iterator>
#include <type_traits>

/// Allows inline transformations on iterators.
/// When the iterator is dereferenced, it is passed through a unary functor of
/// some kind, and the returned value is the output of this functor.
/// Useful for 'pipelining' operations on iterators, or for adapting ranges
/// when passing them to methods in a way that doesn't require a new range to be
/// allocated
template <typename It, typename Mapper>
class mapping_iteratort final
{
public:
  using iterator_category =
    typename std::iterator_traits<It>::iterator_category;

  using value_type = decltype(std::declval<Mapper>()(*std::declval<It>()));
  using difference_type = typename std::iterator_traits<It>::difference_type;
  using reference = typename std::add_lvalue_reference<value_type>::type;
  using pointer = typename std::add_pointer<reference>::type;

  mapping_iteratort() = default;
  explicit mapping_iteratort(It it) : it_(std::move(it))
  {
  }

  explicit mapping_iteratort(It it, Mapper mapper)
    : it_(std::move(it)), mapper_(std::move(mapper))
  {
  }

  template <class U, class V>
  mapping_iteratort(const mapping_iteratort<U, V> &other)
    : it_(other.it_), mapper_(other.mapper_)
  {
  }

  template <class U, class V>
  void swap(mapping_iteratort<U, V> &other)
  {
    using std::swap;
    swap(it_, other.it_);
    swap(mapper_, other.mapper_);
  }

  template <class U, class V>
  mapping_iteratort &operator=(mapping_iteratort<U, V> other)
  {
    swap(other);
    return *this;
  }

  mapping_iteratort(const mapping_iteratort &other)
    : it_(other.it_), mapper_(other.mapper_)
  {
  }

  mapping_iteratort(mapping_iteratort &&other)
    : it_(std::move(other.it_)), mapper_(std::move(other.mapper_))
  {
  }

  mapping_iteratort &operator=(const mapping_iteratort &other)
  {
    auto copy = other;
    swap(copy);
    return *this;
  }

  mapping_iteratort &operator=(mapping_iteratort &&other)
  {
    swap(other);
    return *this;
  }

  It base() const
  {
    return it_;
  }

  value_type operator*() const
  {
    return mapper_(*it_);
  }

  pointer operator->() const
  {
    return &mapper_(*it_);
  }

  value_type operator[](difference_type n) const
  {
    return mapper_(it_[n]);
  }

  mapping_iteratort &operator++()
  {
    ++it_;
    return *this;
  }
  mapping_iteratort &operator--()
  {
    --it_;
    return *this;
  }

  mapping_iteratort operator++(int)
  {
    return mapping_iteratort{it_++, mapper_};
  }
  mapping_iteratort operator--(int)
  {
    return mapping_iteratort{it_--, mapper_};
  }

  mapping_iteratort operator+(difference_type n) const
  {
    auto ret = *this;
    return ret += n;
  }
  mapping_iteratort operator-(difference_type n) const
  {
    auto ret = *this;
    return ret -= n;
  }

  mapping_iteratort &operator+=(difference_type n)
  {
    it_ += n;
    return *this;
  }

  mapping_iteratort &operator-=(difference_type n)
  {
    it_ -= n;
    return *this;
  }

private:
  It it_;
  Mapper mapper_;

  template <typename U, typename V>
  friend class mapping_iteratort;
};

template <class A, class B, class C, class D>
bool operator==(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() == rhs.base();
}

template <class A, class B, class C>
bool operator==(const mapping_iteratort<A, B> &lhs, const C &rhs)
{
  return lhs.base() == rhs;
}

template <class A, class B, class C>
bool operator==(const A &lhs, const mapping_iteratort<B, C> &rhs)
{
  return lhs == rhs.base();
}

template <class A, class B, class C, class D>
bool operator!=(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() != rhs.base();
}

template <class A, class B, class C>
bool operator!=(const mapping_iteratort<A, B> &lhs, const C &rhs)
{
  return lhs.base() != rhs;
}

template <class A, class B, class C>
bool operator!=(const A &lhs, const mapping_iteratort<B, C> &rhs)
{
  return lhs != rhs.base();
}

template <class A, class B, class C, class D>
bool operator<(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() < rhs.base();
}

template <class A, class B, class C, class D>
bool operator<=(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() <= rhs.base();
}

template <class A, class B, class C, class D>
bool operator>(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() > rhs.base();
}

template <class A, class B, class C, class D>
bool operator>=(
  const mapping_iteratort<A, B> &lhs,
  const mapping_iteratort<C, D> &rhs)
{
  return lhs.base() >= rhs.base();
}

template <class U, class V>
mapping_iteratort<U, V> operator+(
  typename mapping_iteratort<U, V>::difference_type n,
  const mapping_iteratort<U, V> &it)
{
  return it + n;
}

template <class U, class V>
mapping_iteratort<U, V> operator-(
  typename mapping_iteratort<U, V>::difference_type n,
  const mapping_iteratort<U, V> &it)
{
  return it - n;
}

template <class U, class V>
typename mapping_iteratort<U, V>::difference_type
operator-(const mapping_iteratort<U, V> &a, const mapping_iteratort<U, V> &b)
{
  return a.base() - b.base();
}

template <class U, class V>
mapping_iteratort<U, V> make_mapping_iterator(U &&it, V &&mapper)
{
  return mapping_iteratort<U, V>{std::forward<U>(it), std::forward<V>(mapper)};
}

#endif
