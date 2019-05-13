/*******************************************************************\

Module: util

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORWARD_LIST_AS_MAP_H
#define CPROVER_UTIL_FORWARD_LIST_AS_MAP_H

#include <algorithm>
#include <forward_list>

#include "as_const.h"
#include "narrow.h"

/// Implementation of map-like interface using a forward list
template <typename keyt, typename mappedt>
//  requires DefaultConstructible<mappedt>
class forward_list_as_mapt : public std::forward_list<std::pair<keyt, mappedt>>
{
public:
  using implementationt = typename std::forward_list<std::pair<keyt, mappedt>>;
  using const_iterator = typename implementationt::const_iterator;
  using iterator = typename implementationt::iterator;

  forward_list_as_mapt() : implementationt()
  {
  }

  forward_list_as_mapt(std::initializer_list<std::pair<keyt, mappedt>> list)
    : implementationt(std::move(list))
  {
  }

  void remove(const keyt &name)
  {
    const_iterator it = this->lower_bound(name);

    if(it != this->end() && it->first == name)
    {
      iterator before = this->before_begin();
      while(std::next(before) != it)
        ++before;
      this->erase_after(before);
    }
  }

  const const_iterator find(const keyt &name) const
  {
    const_iterator it = lower_bound(name);

    if(it == this->end() || it->first != name)
      return this->end();

    return it;
  }

  iterator add(const keyt &name)
  {
    iterator it = mutable_lower_bound(name);

    if(it == this->end() || it->first != name)
    {
      iterator before = this->before_begin();
      while(std::next(before) != it)
        ++before;
      it = this->emplace_after(before, name, mappedt());
    }

    return it;
  }

  mappedt &operator[](const keyt &name)
  {
    return add(name)->second;
  }

  mappedt &add(const keyt &name, mappedt irep)
  {
    iterator it = mutable_lower_bound(name);

    if(it == this->end() || it->first != name)
    {
      iterator before = this->before_begin();
      while(std::next(before) != it)
        ++before;
      it = this->emplace_after(before, name, std::move(irep));
    }
    else
      it->second = std::move(irep);

    return it->second;
  }

  std::size_t size() const
  {
    return narrow<std::size_t>(std::distance(this->begin(), this->end()));
  }

private:
  static bool order(const std::pair<keyt, mappedt> &a, const keyt &b)
  {
    return a.first < b;
  }

  const_iterator lower_bound(const keyt &id) const
  {
    return std::lower_bound(this->begin(), this->end(), id, order);
  }

  iterator mutable_lower_bound(const keyt &id)
  {
    return std::lower_bound(this->begin(), this->end(), id, order);
  }
};

#endif // CPROVER_UTIL_FORWARD_LIST_AS_MAP_H
