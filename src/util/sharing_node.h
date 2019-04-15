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

#include "invariant.h"
#include "make_unique.h"
#include "small_shared_ptr.h"
#include "small_shared_two_way_ptr.h"

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
// clang-format on

#define SN_TYPE_ARGS keyT, valueT, equalT

#define SN_PTR_TYPE_ARGS d_internalt<SN_TYPE_ARGS>, d_containert<SN_TYPE_ARGS>

#define SN_PTR_TYPE_ARG d_leaft<SN_TYPE_ARGS>

template <class T>
const T *as_const(T *t)
{
  return t;
}

// Inner nodes (internal nodes or container nodes)

typedef small_shared_two_way_pointeet<unsigned> d_baset;

SN_TYPE_PAR_DECL class sharing_node_innert;

SN_TYPE_PAR_DECL class d_internalt : public d_baset
{
public:
  typedef sharing_node_innert<SN_TYPE_ARGS> innert;
#if SN_SMALL_MAP == 1
  typedef small_mapt<innert> to_mapt;
#else
  typedef std::map<std::size_t, innert> to_mapt;
#endif

  to_mapt m;
};

SN_TYPE_PAR_DECL class sharing_node_leaft;

SN_TYPE_PAR_DECL class d_containert : public d_baset
{
public:
  typedef sharing_node_leaft<SN_TYPE_ARGS> leaft;
  typedef std::forward_list<leaft> leaf_listt;

  leaf_listt con;
};

class sharing_node_baset
{
};

SN_TYPE_PAR_DEF class sharing_node_innert : public sharing_node_baset
{
public:
  typedef small_shared_two_way_ptrt<SN_PTR_TYPE_ARGS> datat;
  typedef typename datat::use_countt use_countt;

  typedef d_internalt<SN_TYPE_ARGS> d_it;
  typedef d_containert<SN_TYPE_ARGS> d_ct;

  typedef typename d_it::to_mapt to_mapt;

  typedef typename d_ct::leaft leaft;
  typedef typename d_ct::leaf_listt leaf_listt;

  sharing_node_innert()
  {
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

  bool shares_with(const sharing_node_innert &other) const
  {
    SN_ASSERT(data);
    SN_ASSERT(other.data);

    return data == other.data;
  }

  use_countt use_count() const
  {
    return data.use_count();
  }

  void swap(sharing_node_innert &other)
  {
    data.swap(other.data);
  }

  // Types

  bool is_internal() const
  {
    return data.is_derived_u();
  }

  bool is_container() const
  {
    return data.is_derived_v();
  }

  const d_it &read_internal() const
  {
    SN_ASSERT(!empty());

    return *data.get_derived_u();
  }

  const d_ct &read_container() const
  {
    SN_ASSERT(!empty());

    return *data.get_derived_v();
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
    SN_ASSERT(is_container());

    const leaf_listt &c = get_container();

    for(const auto &n : c)
    {
      if(equalT()(n.get_key(), k))
        return &n;
    }

    return nullptr;
  }

  leaft *find_leaf(const keyT &k)
  {
    SN_ASSERT(is_container());

    leaf_listt &c = get_container();

    for(auto &n : c)
    {
      if(equalT()(n.get_key(), k))
        return &n;
    }

    // If we return nullptr the call must be followed by a call to
    // place_leaf(k, ...)
    return nullptr;
  }

  // add leaf, key must not exist yet
  leaft *place_leaf(const keyT &k, const valueT &v)
  {
    SN_ASSERT(is_container());
    // we need to check empty() first as the const version of find_leaf() must
    // not be called on an empty node
    PRECONDITION(empty() || as_const(this)->find_leaf(k) == nullptr);

    leaf_listt &c = get_container();
    c.push_front(leaft(k, v));

    return &c.front();
  }

  // add leaf, key must not exist yet
  leaft *place_leaf(const keyT &k, valueT &&v)
  {
    SN_ASSERT(is_container());
    // we need to check empty() first as the const version of find_leaf() must
    // not be called on an empty node
    PRECONDITION(empty() || as_const(this)->find_leaf(k) == nullptr);

    leaf_listt &c = get_container();
    c.push_front(leaft(k, std::move(v)));

    return &c.front();
  }

  // remove leaf, key must exist
  void remove_leaf(const keyT &k)
  {
    SN_ASSERT(is_container());

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

      if(equalT()(leaf.get_key(), k))
      {
        c.erase_after(last_it);
        return;
      }

      last_it = it;
    }

    UNREACHABLE;
  }

  // Handle children

  const typename d_it::innert *find_child(const std::size_t n) const
  {
    SN_ASSERT(is_internal());

    const to_mapt &m = get_to_map();
    typename to_mapt::const_iterator it = m.find(n);

    if(it != m.end())
      return &it->second;

    return nullptr;
  }

  typename d_it::innert *add_child(const std::size_t n)
  {
    SN_ASSERT(is_internal());

    to_mapt &m = get_to_map();
    return &m[n];
  }

  void remove_child(const std::size_t n)
  {
    SN_ASSERT(is_internal());

    to_mapt &m = get_to_map();
    std::size_t r = m.erase(n);

    SN_ASSERT_USE(r, r == 1);
  }

protected:
  d_it &write_internal()
  {
    if(!data)
    {
      data = make_shared_derived_u<SN_PTR_TYPE_ARGS>();
    }
    else if(data.use_count() > 1)
    {
      data = make_shared_derived_u<SN_PTR_TYPE_ARGS>(*data.get_derived_u());
    }

    SN_ASSERT(data.use_count() == 1);

    return *data.get_derived_u();
  }

  d_ct &write_container()
  {
    if(!data)
    {
      data = make_shared_derived_v<SN_PTR_TYPE_ARGS>();
    }
    else if(data.use_count() > 1)
    {
      data = make_shared_derived_v<SN_PTR_TYPE_ARGS>(*data.get_derived_v());
    }

    SN_ASSERT(data.use_count() == 1);

    return *data.get_derived_v();
  }

  datat data;
};

// Leafs

SN_TYPE_PAR_DECL class d_leaft : public small_shared_pointeet<unsigned>
{
public:
#if SN_SHARE_KEYS == 1
  typedef std::shared_ptr<keyT> keyt;
#else
  typedef keyT keyt;
#endif

  d_leaft(const keyt &k, const valueT &v) : k(k), v(v)
  {
  }
  d_leaft(const keyt &k, valueT &&v) : k(k), v(std::move(v))
  {
  }
  keyt k;

  valueT v;
};

SN_TYPE_PAR_DEF class sharing_node_leaft : public sharing_node_baset
{
public:
  typedef small_shared_ptrt<SN_PTR_TYPE_ARG> datat;
  typedef decltype(datat().use_count()) use_countt;

  typedef d_leaft<SN_TYPE_ARGS> d_lt;

  sharing_node_leaft(const keyT &k, const valueT &v)
  {
    SN_ASSERT(!data);

#if SN_SHARE_KEYS == 1
    SN_ASSERT(d.k == nullptr);
    data = make_small_shared_ptr<d_lt>(std::make_shared<keyT>(k), v);
#else
    data = make_small_shared_ptr<d_lt>(k, v);
#endif
  }

  sharing_node_leaft(const keyT &k, valueT &&v)
  {
    SN_ASSERT(!data);

#if SN_SHARE_KEYS == 1
    SN_ASSERT(d.k == nullptr);
    data = make_small_shared_ptr<d_lt>(std::make_shared<keyT>(k), std::move(v));
#else
    data = make_small_shared_ptr<d_lt>(k, std::move(v));
#endif
  }

  bool shares_with(const sharing_node_leaft &other) const
  {
    return data == other.data;
  }

  use_countt use_count() const
  {
    return data.use_count();
  }

  void swap(sharing_node_leaft &other)
  {
    SN_ASSERT(data);
    SN_ASSERT(other.data);

    data.swap(other.data);
  }

  const d_lt &read() const
  {
    return *data;
  }

  // Accessors

  const keyT &get_key() const
  {
    SN_ASSERT(data);

#if SN_SHARE_KEYS == 1
    return *read().k;
#else
    return read().k;
#endif
  }

  const valueT &get_value() const
  {
    SN_ASSERT(data);

    return read().v;
  }

  valueT &get_value()
  {
    SN_ASSERT(data);

    if(data.use_count() > 1)
    {
      data = make_small_shared_ptr<d_lt>(*data);
    }

    SN_ASSERT(data.use_count() == 1);

    return data->v;
  }

  void set_value(const valueT &v)
  {
    SN_ASSERT(data);

    if(data.use_count() > 1)
    {
      data = make_small_shared_ptr<d_lt>(data->k, v);
    }
    else
    {
      data->v = v;
    }

    SN_ASSERT(data.use_count() == 1);
  }

  void set_value(valueT &&v)
  {
    SN_ASSERT(data);

    if(data.use_count() > 1)
    {
      data = make_small_shared_ptr<d_lt>(data->k, std::move(v));
    }
    else
    {
      data->v = std::move(v);
    }

    SN_ASSERT(data.use_count() == 1);
  }

  void mutate_value(std::function<void(valueT &)> mutator)
  {
    SN_ASSERT(data);

    if(data.use_count() > 1)
      data = make_small_shared_ptr<d_lt>(data->k, data->v);

    mutator(data->v);
  }

protected:
  datat data;
};

#endif
