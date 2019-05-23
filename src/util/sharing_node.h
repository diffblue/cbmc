/*******************************************************************\

Module: Sharing node

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Sharing node

#ifndef CPROVER_UTIL_SHARING_NODE_H
#define CPROVER_UTIL_SHARING_NODE_H

#ifdef SN_DEBUG
#include <iostream>
#endif

#include <forward_list>
#include <type_traits>

#ifndef SN_SMALL_MAP
#define SN_SMALL_MAP 1
#endif

#ifndef SN_SHARE_KEYS
#define SN_SHARE_KEYS 0
#endif

#if SN_SMALL_MAP == 1
#include "small_map.h"
#else
#include <map>
#endif

#include "as_const.h"
#include "invariant.h"
#include "make_unique.h"
#include "small_shared_n_way_ptr.h"
#include "small_shared_ptr.h"

#ifdef SN_INTERNAL_CHECKS
#define SN_ASSERT(b) INVARIANT(b, "Sharing node internal invariant")
#define SN_ASSERT_USE(v, b) SN_ASSERT(b)
#else
#define SN_ASSERT(b)
#define SN_ASSERT_USE(v, b) static_cast<void>(v);
#endif

// clang-format off
#define SN_TYPE_PAR_DECL \
  template <typename keyT, \
            typename valueT, \
            typename equalT = std::equal_to<keyT>>

#define SN_TYPE_PAR_DEF \
  template <typename keyT, typename valueT, typename equalT>

#define SN_TYPE_ARGS keyT, valueT, equalT

#define SN_PTR_TYPE_ARGS \
  d_containert<SN_TYPE_ARGS>, d_leaft<SN_TYPE_ARGS>, d_internalt<SN_TYPE_ARGS>
// clang-format on

typedef small_shared_n_way_pointee_baset<3, unsigned> d_baset;

SN_TYPE_PAR_DECL class sharing_nodet;

SN_TYPE_PAR_DECL class d_internalt : public d_baset
{
public:
  typedef sharing_nodet<SN_TYPE_ARGS> innert;
#if SN_SMALL_MAP == 1
  typedef small_mapt<innert> to_mapt;
#else
  typedef std::map<std::size_t, innert> to_mapt;
#endif

  to_mapt m;
};

SN_TYPE_PAR_DECL class d_containert : public d_baset
{
public:
  typedef sharing_nodet<SN_TYPE_ARGS> leaft;
  typedef std::forward_list<leaft> leaf_listt;

  leaf_listt con;
};

SN_TYPE_PAR_DECL class d_leaft : public d_baset
{
public:
#if SN_SHARE_KEYS == 1
  typedef std::shared_ptr<keyT> keyt;
#else
  typedef keyT keyt;
#endif

  template <class valueU>
  d_leaft(const keyt &k, valueU &&v) : k(k), v(std::forward<valueU>(v))
  {
  }
  keyt k;

  valueT v;
};

SN_TYPE_PAR_DEF class sharing_nodet
{
public:
  typedef small_shared_n_way_ptrt<SN_PTR_TYPE_ARGS> datat;
  typedef typename datat::use_countt use_countt;

  typedef d_internalt<SN_TYPE_ARGS> d_it;
  typedef d_containert<SN_TYPE_ARGS> d_ct;
  typedef d_leaft<SN_TYPE_ARGS> d_lt;

  typedef typename d_it::to_mapt to_mapt;

  typedef typename d_ct::leaft leaft;
  typedef typename d_ct::leaf_listt leaf_listt;

  sharing_nodet()
  {
  }

  template <class valueU>
  sharing_nodet(const keyT &k, valueU &&v)
  {
    SN_ASSERT(!data);

#if SN_SHARE_KEYS == 1
    SN_ASSERT(d.k == nullptr);
    data = make_shared_3<1, SN_PTR_TYPE_ARGS>(
      std::make_shared<keyT>(k), std::forward<valueU>(v));
#else
    data = make_shared_3<1, SN_PTR_TYPE_ARGS>(k, std::forward<valueU>(v));
#endif
  }

  bool empty() const
  {
    return !data;
  }

  void clear()
  {
    // only the root node may be cleared which is an internal node
    SN_ASSERT(is_internal());

    data.reset();
  }

  bool shares_with(const sharing_nodet &other) const
  {
    SN_ASSERT(data);
    SN_ASSERT(other.data);

    return data == other.data;
  }

  use_countt use_count() const
  {
    return data.use_count();
  }

  void swap(sharing_nodet &other)
  {
    data.swap(other.data);
  }

  // Types

  bool is_internal() const
  {
    return data.template is_derived<2>();
  }

  bool is_container() const
  {
    return data.template is_derived<0>();
  }

  bool is_leaf() const
  {
    return data.template is_derived<1>();
  }

  bool is_defined_internal() const
  {
    return !empty() && is_internal();
  }

  bool is_defined_container() const
  {
    return !empty() && is_container();
  }

  bool is_defined_leaf() const
  {
    return !empty() && is_leaf();
  }

  const d_it &read_internal() const
  {
    SN_ASSERT(!empty());

    return *data.template get_derived<2>();
  }

  const d_ct &read_container() const
  {
    SN_ASSERT(!empty());

    return *data.template get_derived<0>();
  }

  const d_lt &read_leaf() const
  {
    SN_ASSERT(!empty());

    return *data.template get_derived<1>();
  }

  // Accessors

  const to_mapt &get_to_map() const
  {
    return read_internal().m;
  }

  to_mapt &get_to_map()
  {
    return write_internal().m;
  }

  const leaf_listt &get_container() const
  {
    return read_container().con;
  }

  leaf_listt &get_container()
  {
    return write_container().con;
  }

  // Containers

  const leaft *find_leaf(const keyT &k) const
  {
    SN_ASSERT(is_defined_container());

    const leaf_listt &c = get_container();

    for(const auto &n : c)
    {
      SN_ASSERT(n.is_leaf());

      if(equalT()(n.get_key(), k))
        return &n;
    }

    return nullptr;
  }

  leaft *find_leaf(const keyT &k)
  {
    SN_ASSERT(is_defined_container());

    leaf_listt &c = get_container();

    for(auto &n : c)
    {
      SN_ASSERT(n.is_leaf());

      if(equalT()(n.get_key(), k))
        return &n;
    }

    UNREACHABLE;
    return nullptr;
  }

  // add leaf, key must not exist yet
  template <class valueU>
  void place_leaf(const keyT &k, valueU &&v)
  {
    SN_ASSERT(is_container()); // empty() is allowed

    // we need to check empty() first as the const version of find_leaf() must
    // not be called on an empty node
    PRECONDITION(empty() || as_const_ptr(this)->find_leaf(k) == nullptr);

    leaf_listt &c = get_container();
    c.emplace_front(k, std::forward<valueU>(v));
    SN_ASSERT(c.front().is_defined_leaf());
  }

  // remove leaf, key must exist
  void remove_leaf(const keyT &k)
  {
    SN_ASSERT(is_defined_container());

    leaf_listt &c = get_container();

    SN_ASSERT(!c.empty());

    const leaft &first = c.front();

    if(equalT()(first.get_key(), k))
    {
      c.pop_front();
      return;
    }

    typename leaf_listt::const_iterator last_it = c.begin();

    typename leaf_listt::const_iterator it = c.begin();
    it++;

    for(; it != c.end(); it++)
    {
      const leaft &leaf = *it;

      SN_ASSERT(leaf.is_defined_leaf());

      if(equalT()(leaf.get_key(), k))
      {
        c.erase_after(last_it);
        return;
      }

      last_it = it;
    }

    UNREACHABLE;
  }

  // Inner nodes

  const typename d_it::innert *find_child(const std::size_t n) const
  {
    SN_ASSERT(is_defined_internal());

    const to_mapt &m = get_to_map();
    typename to_mapt::const_iterator it = m.find(n);

    if(it != m.end())
      return &it->second;

    return nullptr;
  }

  typename d_it::innert &add_child(const std::size_t n)
  {
    SN_ASSERT(is_internal()); // empty() is allowed

    to_mapt &m = get_to_map();
    return m[n];
  }

  void remove_child(const std::size_t n)
  {
    SN_ASSERT(is_defined_internal());

    to_mapt &m = get_to_map();
    std::size_t r = m.erase(n);

    SN_ASSERT_USE(r, r == 1);
  }

  // Leafs

  const keyT &get_key() const
  {
    SN_ASSERT(is_defined_leaf());

#if SN_SHARE_KEYS == 1
    return *read_leaf().k;
#else
    return read_leaf().k;
#endif
  }

  const valueT &get_value() const
  {
    SN_ASSERT(is_defined_leaf());

    return read_leaf().v;
  }

  template <class valueU>
  void make_leaf(const keyT &k, valueU &&v)
  {
    SN_ASSERT(!data);

    data = make_shared_3<1, SN_PTR_TYPE_ARGS>(k, std::forward<valueU>(v));
  }

  template <class valueU>
  void set_value(valueU &&v)
  {
    SN_ASSERT(is_defined_leaf());

    if(data.use_count() > 1)
    {
      data =
        make_shared_3<1, SN_PTR_TYPE_ARGS>(get_key(), std::forward<valueU>(v));
    }
    else
    {
      data.template get_derived<1>()->v = std::forward<valueU>(v);
    }

    SN_ASSERT(data.use_count() == 1);
  }

  void mutate_value(std::function<void(valueT &)> mutator)
  {
    SN_ASSERT(is_defined_leaf());

    if(data.use_count() > 1)
    {
      data = make_shared_3<1, SN_PTR_TYPE_ARGS>(read_leaf());
    }

    mutator(data.template get_derived<1>()->v);

    SN_ASSERT(data.use_count() == 1);
  }

protected:
  d_it &write_internal()
  {
    SN_ASSERT(is_internal());

    if(!data)
    {
      data = make_shared_3<2, SN_PTR_TYPE_ARGS>();
    }
    else if(data.use_count() > 1)
    {
      data = make_shared_3<2, SN_PTR_TYPE_ARGS>(read_internal());
    }

    SN_ASSERT(data.use_count() == 1);

    return *data.template get_derived<2>();
  }

  d_ct &write_container()
  {
    SN_ASSERT(is_container());

    if(!data)
    {
      data = make_shared_3<0, SN_PTR_TYPE_ARGS>();
    }
    else if(data.use_count() > 1)
    {
      data = make_shared_3<0, SN_PTR_TYPE_ARGS>(read_container());
    }

    SN_ASSERT(data.use_count() == 1);

    return *data.template get_derived<0>();
  }

  datat data;
};

#endif
