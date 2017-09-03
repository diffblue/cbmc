/*******************************************************************\

Module: Sharing node

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Sharing node

#ifndef CPROVER_UTIL_SHARING_NODE_H
#define CPROVER_UTIL_SHARING_NODE_H

#include <list>
#include <map>
#include <memory>
#include <cassert>

#include "invariant.h"

#define _sn_assert(b) assert(b)
//#define _sn_assert(b)

template <class T>
const T *as_const(T *t)
{
  return t;
}

template <
  class keyT,
  class valueT,
  class predT=std::equal_to<keyT>,
  bool no_sharing=false>
class sharing_nodet
{
public:
  friend void sharing_node_test();

  typedef keyT key_type;
  typedef valueT mapped_type;

  typedef predT key_equal;

  typedef sharing_nodet<key_type, mapped_type, key_equal> self_type;

  typedef std::map<unsigned, self_type> subt;
  typedef std::list<self_type> containert;

  typedef const std::pair<const self_type &, const bool> const_find_type;
  typedef const std::pair<self_type &, const bool> find_type;

  sharing_nodet() : data(empty_data)
  {
    _sn_assert(data.use_count()>=2);
  }

  sharing_nodet(const key_type &k, const mapped_type &m) : data(empty_data)
  {
    _sn_assert(data.use_count()>=2);

    dt &d=write();

    _sn_assert(d.k==nullptr);
    d.k=std::make_shared<key_type>(k);

    _sn_assert(d.m==nullptr);
    d.m.reset(new mapped_type(m));
  }

  sharing_nodet(const self_type &other)
  {
#ifdef SM_NO_SHARING
    data=std::make_shared<dt>(*other.data);
#else
    if(no_sharing)
    {
      data=std::make_shared<dt>(*other.data);
    }
    else
    {
      data=other.data;
    }
#endif
  }

  // check type of node

  bool is_empty() const
  {
    _sn_assert(is_well_formed());
    return data==empty_data;
  }

  bool is_internal() const
  {
    _sn_assert(is_well_formed());
    _sn_assert(!is_empty());
    return !get_sub().empty();
  }

  bool is_container() const
  {
    _sn_assert(is_well_formed());
    _sn_assert(!is_empty());
    return !get_container().empty();
  }

  bool is_leaf() const
  {
    _sn_assert(is_well_formed());
    _sn_assert(!is_empty());
    return read().is_leaf();
  }

  // accessors

  const key_type &get_key() const
  {
    _sn_assert(is_leaf());
    return *read().k;
  }

  const mapped_type &get_value() const
  {
    _sn_assert(is_leaf());
    return *read().m;
  }

  mapped_type &get_value()
  {
    _sn_assert(is_leaf());
    return *write().m;
  }

  subt &get_sub()
  {
    return write().sub;
  }

  const subt &get_sub() const
  {
    return read().sub;
  }

  containert &get_container()
  {
    return write().con;
  }

  const containert &get_container() const
  {
    return read().con;
  }

  // internal nodes

  const self_type *find_child(const unsigned n) const
  {
    const subt &s=get_sub();
    typename subt::const_iterator it=s.find(n);

    if(it!=s.end())
      return &it->second;

    return nullptr;
  }

  self_type *add_child(const unsigned n)
  {
    subt &s=get_sub();
    return &s[n];
  }

  void remove_child(const unsigned n)
  {
    subt &s=get_sub();
    size_t r=s.erase(n);

    _sn_assert(r==1);
  }

  // container nodes

  const self_type *find_leaf(const key_type &k) const
  {
    const containert &c=get_container();

    for(const auto &n : c)
    {
      if(key_equal()(n.get_key(), k))
        return &n;
    }

    return nullptr;
  }

  self_type *find_leaf(const key_type &k)
  {
    containert &c=get_container();

    for(auto &n : c)
    {
      if(key_equal()(n.get_key(), k))
        return &n;
    }

    return nullptr;
  }

  // add leaf, key must not exist yet
  self_type *place_leaf(const key_type &k, const mapped_type &m)
  {
    _sn_assert(as_const(this)->find_leaf(k)==nullptr);

    containert &c=get_container();
    c.push_back(self_type(k, m));

    return &c.back();
  }

  // remove leaf, key must exist
  void remove_leaf(const key_type &k)
  {
    containert &c=get_container();

    for(typename containert::const_iterator it=c.begin();
        it!=c.end(); it++)
    {
      const self_type &n=*it;

      if(key_equal()(n.get_key(), k))
      {
        c.erase(it);
        return;
      }
    }

    UNREACHABLE;
  }

  // misc

  void clear()
  {
    *this=self_type();
  }

  bool shares_with(const self_type &other) const
  {
    return data==other.data;
  }

  void swap(self_type &other)
  {
    data.swap(other.data);
  }

protected:
  class dt
  {
  public:
    dt() {}

    dt(const dt &d) : k(d.k), sub(d.sub), con(d.con)
    {
      if(d.is_leaf())
      {
        _sn_assert(m==nullptr);
        m.reset(new mapped_type(*d.m));
      }
    }

    bool is_leaf() const
    {
      _sn_assert(k==nullptr || m!=nullptr);
      return k!=nullptr;
    }

    std::shared_ptr<key_type> k;
    std::unique_ptr<mapped_type> m;

    subt sub;
    containert con;
  };

  const dt &read() const
  {
    return *data;
  }

  dt &write()
  {
    detach();
    return *data;
  }

  void detach()
  {
    _sn_assert(data.use_count()>0);

    if(data==empty_data)
      data=std::make_shared<dt>();
    else if(data.use_count()>1)
      data=std::make_shared<dt>(*data);

    _sn_assert(data.use_count()==1);
  }

  bool is_well_formed() const
  {
    if(data==nullptr)
      return false;

    const dt &d=*data;

    bool b;

    // empty node
    b=data==empty_data;
    // internal node
    b|=d.k==nullptr && d.m==nullptr && get_container().empty() &&
       !get_sub().empty();
    // container node
    b|=d.k==nullptr && d.m==nullptr && !get_container().empty() &&
       get_sub().empty();
    // leaf node
    b|=d.k!=nullptr && d.m!=nullptr && get_container().empty() &&
       get_sub().empty();

    return b;
  }

  std::shared_ptr<dt> data;
  static std::shared_ptr<dt> empty_data;

  // dummy node returned when node was not found
  static sharing_nodet dummy;
};

template <class keyT, class valueT, class predT, bool no_sharing>
std::shared_ptr<typename sharing_nodet<keyT, valueT, predT, no_sharing>::dt>
  sharing_nodet<keyT, valueT, predT, no_sharing>::empty_data(
    new sharing_nodet<keyT, valueT, predT, no_sharing>::dt());

template <class keyT, class valueT, class predT, bool no_sharing>
sharing_nodet<keyT, valueT, predT, no_sharing>
  sharing_nodet<keyT, valueT, predT, no_sharing>::dummy;

#endif
