/*******************************************************************\

Module: Sharing map

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Sharing map

#ifndef CPROVER_UTIL_SHARING_MAP_H
#define CPROVER_UTIL_SHARING_MAP_H

#include <string>
#include <stack>
#include <vector>
#include <map>
#include <stdexcept>
#include <functional>
#include <memory>
#include <iosfwd>
#include <cassert>

#include <util/string2int.h>
#include <util/threeval.h>
#include <util/irep.h>
#include <util/sharing_node.h>

#define _sm_assert(b) assert(b)
//#define _sm_assert(b)

#define SHARING_MAPT(R) \
  template <class keyT, class valueT, class hashT, class predT> \
  R sharing_mapt<keyT, valueT, hashT, predT>

#define SHARING_MAPT2(CV, ST) \
  template <class keyT, class valueT, class hashT, class predT> \
  CV typename sharing_mapt<keyT, valueT, hashT, predT>::ST \
  sharing_mapt<keyT, valueT, hashT, predT>

template <
  class keyT,
  class valueT,
  class hashT=std::hash<keyT>,
  class predT=std::equal_to<keyT>>
class sharing_mapt
{
public:
  friend void sharing_map_interface_test();
  friend void sharing_map_copy_test();
  friend void sharing_map_collision_test();
  friend void sharing_map_view_test();

  ~sharing_mapt()
  {
  }

  using key_type = keyT;
  using mapped_type = valueT;
  using value_type = std::pair<const key_type, mapped_type>;

  using hash = hashT;
  using key_equal = predT;

  using self_type = sharing_mapt<key_type, mapped_type, hash, key_equal>;
  using node_type = sharing_nodet<key_type, mapped_type, key_equal>;

  using size_type = size_t;

  using const_find_type = const std::pair<const mapped_type &, const bool>;
  using find_type = const std::pair<mapped_type &, const bool>;

  using keyst = std::vector<key_type>;

  using subt = typename node_type::subt;
  using containert = typename node_type::containert;

  // key-value map
  node_type map;

  // number of elements in the map
  size_type num=0;

  // dummy element returned when no element was found
  static mapped_type dummy;

  // compile-time configuration

  static const std::string not_found_msg;

  static const size_t bits;
  static const size_t chunk;

  static const size_t mask;
  static const size_t steps;

  // interface

  size_type erase(
    const key_type &k,
    const tvt &key_exists=tvt::unknown());

  size_type erase_all(
    const keyst &ks,
    const tvt &key_exists=tvt::unknown()); // applies to all keys

  // return true if element was inserted
  const_find_type insert(
    const key_type &k,
    const mapped_type &v,
    const tvt &key_exists=tvt::unknown());

  const_find_type insert(
    const value_type &p,
    const tvt &key_exists=tvt::unknown());

  find_type place(
    const key_type &k,
    const mapped_type &v);

  find_type place(
    const value_type &p);

  find_type find(
    const key_type &k,
    const tvt &key_exists=tvt::unknown());

  const_find_type find(const key_type &k) const;

  mapped_type &at(
    const key_type &k,
    const tvt &key_exists=tvt::unknown());

  const mapped_type &at(const key_type &k) const;

  mapped_type &operator[](const key_type &k);

  void swap(self_type &other)
  {
    map.swap(other.map);

    size_t tmp=num;
    num=other.num;
    other.num=tmp;
  }

  size_type size() const
  {
    return num;
  }

  bool empty() const
  {
    return num==0;
  }

  void clear()
  {
    map.clear();
    num=0;
  }

  bool has_key(const key_type &k) const
  {
    return get_leaf_node(k)!=nullptr;
  }

  // views

  using view_itemt = std::pair<const key_type &, const mapped_type &>;
  using viewt = std::vector<view_itemt>;

  class delta_view_itemt
  {
  public:
    delta_view_itemt(
      const bool in_both,
      const key_type &k,
      const mapped_type &m,
      const mapped_type &other_m) :
        in_both(in_both),
        k(k),
        m(m),
        other_m(other_m) {}

    // if true key is in both maps, if false key is only in the map
    // from which the view was obtained
    const bool in_both;

    const key_type &k;

    const mapped_type &m;
    const mapped_type &other_m;
  };

  using delta_viewt = std::vector<delta_view_itemt>;

  void get_view(viewt &view) const;

  void get_delta_view(
    const self_type &other,
    delta_viewt &delta_view,
    const bool only_common=true) const;

protected:
  // helpers

  node_type *get_container_node(const key_type &k);
  const node_type *get_container_node(const key_type &k) const;

  const node_type *get_leaf_node(const key_type &k) const;

  void gather_all(const node_type &n, delta_viewt &delta_view) const;
};

SHARING_MAPT(void)::get_view(viewt &view) const
{
  assert(view.empty());

  std::stack<const node_type *> stack;

  if(empty())
    return;

  stack.push(&map);

  do
  {
    const node_type *n=stack.top();
    stack.pop();

    if(n->is_container())
    {
      for(const auto &child : n->get_container())
      {
        view.push_back(view_itemt(child.get_key(), child.get_value()));
      }
    }
    else
    {
      assert(n->is_internal());

      for(const auto &child : n->get_sub())
      {
        stack.push(&child.second);
      }
    }
  }
  while(!stack.empty());
}

SHARING_MAPT(void)::gather_all(const node_type &n, delta_viewt &delta_view)
  const
{
  std::stack<const node_type *> stack;
  stack.push(&n);

  do
  {
    const node_type *n=stack.top();
    stack.pop();

    if(n->is_container())
    {
      for(const auto &child : n->get_container())
      {
        delta_view.push_back(
          delta_view_itemt(
            false,
            child.get_key(),
            child.get_value(),
            dummy));
      }
    }
    else
    {
      assert(n->is_internal());

      for(const auto &child : n->get_sub())
      {
        stack.push(&child.second);
      }
    }
  }
  while(!stack.empty());
}

SHARING_MAPT(void)::get_delta_view(
  const self_type &other,
  delta_viewt &delta_view,
  const bool only_common) const
{
  assert(delta_view.empty());

  using stack_itemt = std::pair<const node_type *, const node_type *>;
  std::stack<stack_itemt> stack;

  if(empty())
    return;

  if(other.empty())
  {
    if(!only_common)
    {
      gather_all(map, delta_view);
    }
    return;
  }

  stack.push(stack_itemt(&map, &other.map));

  do
  {
    const stack_itemt si=stack.top();
    stack.pop();

    const node_type *n1=si.first;
    const node_type *n2=si.second;

    if(n1->is_internal())
    {
      _sn_assert(n2->is_internal());

      for(const auto &child : n1->get_sub())
      {
        const node_type *p;

        p=n2->find_child(child.first);
        if(p==nullptr)
        {
          if(!only_common)
          {
            gather_all(child.second, delta_view);
          }
        }
        else if(!child.second.shares_with(*p))
        {
          stack.push(stack_itemt(&child.second, p));
        }
      }
    }
    else if(n1->is_container())
    {
      _sn_assert(n2->is_container());

      for(const auto &l1 : n1->get_container())
      {
        const key_type &k1=l1.get_key();
        bool found=false;

        for(const auto &l2 : n2->get_container())
        {
          const key_type &k2=l2.get_key();

          if(l1.shares_with(l2))
          {
            found=true;
            break;
          }

          if(key_equal()(k1, k2))
          {
            delta_view.push_back(
              delta_view_itemt(
                true,
                k1,
                l1.get_value(),
                l2.get_value()));

            found=true;
            break;
          }
        }

        if(!only_common && !found)
        {
          delta_view.push_back(
            delta_view_itemt(
              false,
              l1.get_key(),
              l1.get_value(),
              dummy));
        }
      }
    }
    else
    {
      UNREACHABLE;
    }
  }
  while(!stack.empty());
}

SHARING_MAPT2(, node_type *)::get_container_node(const key_type &k)
{
  size_t key=hash()(k);
  node_type *p=&map;

  for(unsigned i=0; i<steps; i++)
  {
    unsigned bit=key&mask;
    key>>=chunk;

    p=p->add_child(bit);
  }

  return p;
}

SHARING_MAPT2(const, node_type *)::get_container_node(const key_type &k) const
{
  size_t key=hash()(k);
  const node_type *p=&map;

  for(unsigned i=0; i<steps; i++)
  {
    unsigned bit=key&mask;
    key>>=chunk;

    p=p->find_child(bit);
    if(p==nullptr)
      return nullptr;
  }

  assert(p->is_container());

  return p;
}

SHARING_MAPT2(const, node_type *)::get_leaf_node(const key_type &k) const
{
  const node_type *p=get_container_node(k);
  if(p==nullptr)
    return nullptr;

  p=p->find_leaf(k);

  return p;
}

SHARING_MAPT2(, size_type)::erase(
  const key_type &k,
  const tvt &key_exists)
{
  assert(!key_exists.is_false());

  // check if key exists
  if(key_exists.is_unknown() && !has_key(k))
    return 0;

  node_type *del=nullptr;
  unsigned del_bit;

  size_t key=hash()(k);
  node_type *p=&map;

  for(unsigned i=0; i<steps; i++)
  {
    unsigned bit=key&mask;
    key>>=chunk;

    const subt &sub=as_const(p)->get_sub();
    if(sub.size()>1 || del==nullptr)
    {
      del=p;
      del_bit=bit;
    }

    p=p->add_child(bit);
  }

  _sm_assert(p->is_container());

  {
    const containert &c=as_const(p)->get_container();

    if(c.size()==1)
    {
      del->remove_child(del_bit);
      num--;
      return 1;
    }
  }

  containert &c=p->get_container();
  _sm_assert(c.size()>1);
  p->remove_leaf(k);
  num--;

  return 1;
}

SHARING_MAPT2(, size_type)::erase_all(
  const keyst &ks,
  const tvt &key_exists)
{
  size_type cnt=0;

  for(const key_type &k : ks)
  {
    cnt+=erase(k, key_exists);
  }

  return cnt;
}

SHARING_MAPT2(, const_find_type)::insert(
  const key_type &k,
  const mapped_type &m,
  const tvt &key_exists)
{
  _sn_assert(!key_exists.is_true());

  if(key_exists.is_unknown())
  {
    const node_type *p=as_const(this)->get_leaf_node(k);
    if(p!=nullptr)
      return const_find_type(p->get_value(), false);
  }

  node_type *p=get_container_node(k);
  _sn_assert(p!=nullptr);

  p=p->place_leaf(k, m);
  num++;

  return const_find_type(as_const(p)->get_value(), true);
}

SHARING_MAPT2(, const_find_type)::insert(
  const value_type &p,
  const tvt &key_exists)
{
  return insert(p.first, p.second, key_exists);
}

SHARING_MAPT2(, find_type)::place(
  const key_type &k,
  const mapped_type &m)
{
  node_type *c=get_container_node(k);
  _sm_assert(c!=nullptr);

  node_type *p=c->find_leaf(k);

  if(p!=nullptr)
    return find_type(p->get_value(), false);

  p=c->place_leaf(k, m);
  num++;

  return find_type(p->get_value(), true);
}

SHARING_MAPT2(, find_type)::place(
  const value_type &p)
{
  return place(p.first, p.second);
}

SHARING_MAPT2(, find_type)::find(
  const key_type &k,
  const tvt &key_exists)
{
  _sm_assert(!key_exists.is_false());

  if(key_exists.is_unknown() && !has_key(k))
    return find_type(dummy, false);

  node_type *p=get_container_node(k);
  _sm_assert(p!=nullptr);

  p=p->find_leaf(k);
  _sm_assert(p!=nullptr);

  return find_type(p->get_value(), true);

}

SHARING_MAPT2(, const_find_type)::find(const key_type &k) const
{
  const node_type *p=get_leaf_node(k);

  if(p==nullptr)
    return const_find_type(dummy, false);

  return const_find_type(p->get_value(), true);
}

SHARING_MAPT2(, mapped_type &)::at(
  const key_type &k,
  const tvt &key_exists)
{
  find_type r=find(k, key_exists);

  if(!r.second)
    throw std::out_of_range(not_found_msg);

  return r.first;
}

SHARING_MAPT2(const, mapped_type &)::at(const key_type &k) const
{
  const_find_type r=find(k);
  if(!r.second)
    throw std::out_of_range(not_found_msg);

  return r.first;
}

SHARING_MAPT2(, mapped_type &)::operator[](const key_type &k)
{
  return place(k, mapped_type()).first;
}

// static constants

SHARING_MAPT(const std::string)::not_found_msg="key not found";

// config
SHARING_MAPT(const size_t)::bits=18;
SHARING_MAPT(const size_t)::chunk=3;

// derived config
SHARING_MAPT(const size_t)::mask=0xffff>>(16-chunk);
SHARING_MAPT(const size_t)::steps=bits/chunk;

SHARING_MAPT2(, mapped_type)::dummy;

#endif
