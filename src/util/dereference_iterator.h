/*******************************************************************\

Module: Iterator utilities

Author: @reuk

\*******************************************************************/

#ifndef CPROVER_UTIL_DEREFERENCE_ITERATOR_H
#define CPROVER_UTIL_DEREFERENCE_ITERATOR_H

#include "util/mapping_iterator.h"

namespace detail // NOLINT
{
struct dereft final
{
  template <typename T>
  decltype(*std::declval<T>()) operator()(T &t) const
  {
    return *t;
  }
};
} // namespace detail

template <typename It>
using dereference_iteratort = mapping_iteratort<It, detail::dereft>; // NOLINT

template <typename It>
dereference_iteratort<It> make_dereference_iterator(It &&it)
{
  return dereference_iteratort<It>{std::forward<It>(it)};
}

template <typename T>
class dereference_facadet final
{
public:
  explicit dereference_facadet(T &t) : t_(t)
  {
  }

  using iterator = dereference_iteratort<decltype(begin(std::declval<T>()))>;

  iterator begin() const
  {
    using std::begin;
    return iterator{begin(t_)};
  }

  iterator end() const
  {
    using std::end;
    return iterator{end(t_)};
  }

private:
  T &t_;
};

template <typename T>
dereference_facadet<T> make_dereference_facade(T &t)
{
  return dereference_facadet<T>{t};
}

#endif
