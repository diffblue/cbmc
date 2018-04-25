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

// Note: Due to a bug in Visual Studio we need to add an additional "const"
// qualifier to the return values of insert(), place(), and find(). The type
// defined in sharing_mapt already includes the const qualifier, but it is lost
// when accessed from outside the class. This is fixed in Visual Studio 15.6.

/// A map implemented as a tree where subtrees can be shared between different
/// maps.
///
/// The map is implemented as a fixed-height n-ary trie. The height H and the
/// maximum number of children per inner node S are determined by the two
/// configuration parameters `bits` and `chunks` in sharing_map.h. It holds
/// that H = `bits` / `chunks` and S = 2 ^ `chunks`.
///
/// When inserting a key-value pair into the map, first the hash of its key is
/// computed. The `bits` number of lower order bits of the hash are deemed
/// significant, and are grouped into `bits` / `chunk` chunks. The hash is then
/// treated as a string (with each chunk representing a character) for the
/// purposes of determining the position of the key-value pair in the trie. The
/// actual key-value pairs are stored in the leaf nodes. Collisions (i.e., two
/// different keys yield the same "string"), are handled by chaining the
/// corresponding key-value pairs in a `std::list`.
///
/// The use of a trie in combination with hashing has the advantage that the
/// tree is unlikely to degenerate (if the number of hash collisions is low).
/// This makes re-balancing operations unnecessary which do not interact well
/// with sharing. A disadvantage is that the height of the tree is likely
/// greater than if the elements had been stored in a balanced tree (with
/// greater differences for sparser maps).
///
/// The nodes in the sharing map are objects of type sharing_nodet. Each sharing
/// node has a `shared_ptr` to an object of type `dt` which can be shared
/// between nodes.
///
/// Sharing is initially generated when a map is assigned to another map or
/// copied via the copy constructor. Then both maps contain a pointer to the
/// root node of the tree that represents the maps. On subsequent modifications
/// to one of the maps, nodes are copied and sharing is lessened as described in
/// the following.
///
/// Retrieval, insertion, and removal operations interact with sharing as
/// follows:
/// - When a non-const reference to a value in the map that is contained in a
/// shared subtree is retrieved, the nodes on the path from the root of the
/// subtree to the corresponding key-value pair (and the key-value pair itself)
/// are copied and integrated with the map.
/// - When a key-value pair is inserted into the map and its position is in a
/// shared subtree, already existing nodes from the root of the subtree to the
/// position of the key-value pair are copied and integrated with the map, and
/// new nodes are created as needed.
/// - When a key-value pair is erased from the map that is in a shared subtree,
/// nodes from the root of the subtree to the last node that will still exist on
/// the path to the erased element after the element has been removed are
/// copied and integrated with the map, and the remaining nodes are removed.
///
/// Several methods take a hint indicating whether the element is known not to
/// be in the map (`false`), known to be in the map (`true`), or it is unknown
/// whether the element is in the map (`unknown`). The value `unknown` is always
/// valid. When `true` or `false` are given they need to be accurate, otherwise
/// the behavior is undefined. A correct hint can prevent the need to follow a
/// path from the root to a key-value pair twice (e.g., once for checking that
/// it exists, and second for copying nodes).
///
/// In the descriptions of the methods of the sharing map we also give the
/// complexity of the operations. We use the following symbols:
/// - N: number of key-value pairs in the map
/// - M: maximum number of key-value pairs that are chained in a leaf node
/// - H: height of the tree
/// - S: maximum number of children per internal node
///
/// The first two symbols denote dynamic properties of a given map, whereas the
/// last two symbols are static configuration parameters of the map class.
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

  typedef keyT key_type;
  typedef valueT mapped_type;
  typedef std::pair<const key_type, mapped_type> value_type;

  typedef hashT hash;
  typedef predT key_equal;

  typedef sharing_mapt<key_type, mapped_type, hash, key_equal> self_type;
  typedef sharing_nodet<key_type, mapped_type, key_equal> node_type;

  typedef std::size_t size_type;

  /// Return type of methods that retrieve a const reference to a value. First
  /// component is a reference to the value (or a dummy value if the given key
  /// does not exist), and the second component indicates if the value with the
  /// given key was found.
  typedef const std::pair<const mapped_type &, const bool> const_find_type;

  /// Return type of methods that retrieve a reference to a value. First
  /// component is a reference to the value (or a dummy value if the given key
  /// does not exist), and the second component indicates if the value with the
  /// given key was found.
  typedef const std::pair<mapped_type &, const bool> find_type;

  typedef std::vector<key_type> keyst;

  typedef typename node_type::subt subt;
  typedef typename node_type::containert containert;

  // key-value map
  node_type map;

  // number of elements in the map
  size_type num=0;

  // dummy element returned when no element was found
  static mapped_type dummy;

  // compile-time configuration

  static const std::string not_found_msg;

  /// Number of bits in the hash deemed significant
  static const std::size_t bits;

  /// Size of a chunk of the hash that represents a character
  static const std::size_t chunk;

  static const std::size_t mask;
  static const std::size_t steps;

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

  /// Swap with other map
  ///
  /// Complexity: O(1)
  void swap(self_type &other)
  {
    map.swap(other.map);

    size_t tmp=num;
    num=other.num;
    other.num=tmp;
  }

  /// Get number of elements in map
  ///
  /// Complexity: O(1)
  size_type size() const
  {
    return num;
  }

  /// Check if map is empty
  bool empty() const
  {
    return num==0;
  }

  /// Clear map
  void clear()
  {
    map.clear();
    num=0;
  }

  /// Check if key is in map
  ///
  /// Complexity:
  /// - Worst case: O(H * log(S) + M)
  /// - Best case: O(H)
  bool has_key(const key_type &k) const
  {
    return get_leaf_node(k)!=nullptr;
  }

  // views

  typedef std::pair<const key_type &, const mapped_type &> view_itemt;

  /// View of the key-value pairs in the map. A view is a list of pairs with
  /// the components being const references to the keys and values in the map.
  typedef std::vector<view_itemt> viewt;

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

  /// Delta view of the key-value pairs in two maps. A delta view of two maps is
  /// a view of the key-value pairs in the maps that are contained in subtrees
  /// that are not shared between them (also see get_delta_view()).
  typedef std::vector<delta_view_itemt> delta_viewt;

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

/// Get a view of the elements in the map
/// A view is a list of pairs with the components being const references to the
/// keys and values in the map.
///
/// Complexity:
/// - Worst case: O(N * H * log(S))
/// - Best case: O(N + H)
///
/// \param[out] view: Empty view
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

/// Get a delta view of the elements in the map
///
/// Informally, a delta view of two maps is a view of the key-value pairs in the
/// maps that are contained in subtrees that are not shared between them.
///
/// A delta view is represented as a list of structs, with each struct having
/// four members (`in_both`, `key`, `value1`, `value2`). The elements `key`,
/// `value1`, and `value2` are const references to the corresponding elements in
/// the map. The first element indicates whether the key exists in both maps,
/// the second element is the key, the third element is the mapped value of the
/// first map, and the fourth element is the mapped value of the second map, or
/// a dummy element if the key exists only in the first map (in which case
/// `in_both` is false).
///
/// Calling `A.delta_view(B, ...)` yields a view such that for each element in
/// the view one of two things holds:
/// - the key is contained in both A and B, and in the maps the corresponding
///   key-value pairs are not contained in a subtree that is shared between them
/// - the key is only contained in A
///
/// When `only_common=true`, the first case above holds for every element in the
/// view.
///
/// Complexity:
/// - Worst case: O(max(N1, N2) * H * log(S) * M1 * M2) (no sharing)
/// - Best case: O(1) (maximum sharing)
///
/// The symbols N1, M1 refer to map A, and symbols N2, M2 refer to map B.
///
/// \param other: other map
/// \param[out] delta_view: Empty delta view
/// \param only_common: Indicates if the returned delta view should only
///   contain key-value pairs for keys that exist in both maps
SHARING_MAPT(void)::get_delta_view(
  const self_type &other,
  delta_viewt &delta_view,
  const bool only_common) const
{
  assert(delta_view.empty());

  typedef std::pair<const node_type *, const node_type *> stack_itemt;
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

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;
    key>>=chunk;

    p=p->add_child(bit);
  }

  return p;
}

SHARING_MAPT2(const, node_type *)::get_container_node(const key_type &k) const
{
  size_t key=hash()(k);
  const node_type *p=&map;

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;
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

/// Erase element
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element to erase
/// \param key_exists: Hint to indicate whether the element is known to exist
///   (possible values `unknown` or` true`)
SHARING_MAPT2(, size_type)::erase(
  const key_type &k,
  const tvt &key_exists)
{
  assert(!key_exists.is_false());

  // check if key exists
  if(key_exists.is_unknown() && !has_key(k))
    return 0;

  node_type *del=nullptr;
  std::size_t del_bit = 0;

  size_t key=hash()(k);
  node_type *p=&map;

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;
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

  const containert &c = as_const(p)->get_container();

  if(c.size() == 1)
  {
    del->remove_child(del_bit);
    num--;
    return 1;
  }

  _sm_assert(c.size()>1);
  p->remove_leaf(k);
  num--;

  return 1;
}

/// Erase all elements
///
/// Complexity:
/// - Worst case: O(K * (H * S + M))
/// - Best case: O(K * H)
///
/// \param ks: The keys of the element to erase
/// \param key_exists: Hint to indicate whether the elements are known to exist
///   (possible values `unknown` or `true`). Applies to all elements (i.e., have
///   to use `unknown` if for at least one element it is not known whether it
///   exists)
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

/// Insert element, return const reference
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element to insert
/// \param m: The mapped value to insert
/// \param key_exists: Hint to indicate whether the element is known to exist
///   (possible values `false` or `unknown`)
/// \return Pair of const reference to existing or newly inserted element, and
///   boolean indicating if new element was inserted
SHARING_MAPT2(const, const_find_type)
::insert(const key_type &k, const mapped_type &m, const tvt &key_exists)
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

// Insert element, return const reference
SHARING_MAPT2(const, const_find_type)
::insert(const value_type &p, const tvt &key_exists)
{
  return insert(p.first, p.second, key_exists);
}

/// Insert element, return non-const reference
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element to insert
/// \param m: The mapped value to insert
/// \return Pair of reference to existing or newly inserted element, and boolean
///   indicating if new element was inserted
SHARING_MAPT2(const, find_type)::place(const key_type &k, const mapped_type &m)
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

/// Insert element, return non-const reference
SHARING_MAPT2(const, find_type)::place(const value_type &p)
{
  return place(p.first, p.second);
}

/// Find element
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element to search for
/// \param key_exists: Hint to indicate whether the element is known to exist
///   (possible values `unknown` or `true`)
/// \return Pair of reference to found value (or dummy value if not found), and
///   boolean indicating if element was found.
SHARING_MAPT2(const, find_type)::find(const key_type &k, const tvt &key_exists)
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

/// Find element
///
/// Complexity:
/// - Worst case: O(H * log(S) + M)
/// - Best case: O(H)
///
/// \param k: The key of the element to search
/// \return Pair of const reference to found value (or dummy value if not
///   found), and boolean indicating if element was found.
SHARING_MAPT2(const, const_find_type)::find(const key_type &k) const
{
  const node_type *p=get_leaf_node(k);

  if(p==nullptr)
    return const_find_type(dummy, false);

  return const_find_type(p->get_value(), true);
}

/// Get element at key
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element
/// \param key_exists: Hint to indicate whether the element is known to exist
///   (possible values `unknown` or `true`)
/// \throw `std::out_of_range` if key not found
/// \return The mapped value
SHARING_MAPT2(, mapped_type &)::at(
  const key_type &k,
  const tvt &key_exists)
{
  find_type r=find(k, key_exists);

  if(!r.second)
    throw std::out_of_range(not_found_msg);

  return r.first;
}

/// Get element at key
///
/// Complexity:
/// - Worst case: O(H * log(S) + M)
/// - Best case: O(H)
///
/// \param k: The key of the element
/// \throw std::out_of_range if key not found
/// \return The mapped value
SHARING_MAPT2(const, mapped_type &)::at(const key_type &k) const
{
  const_find_type r=find(k);
  if(!r.second)
    throw std::out_of_range(not_found_msg);

  return r.first;
}

/// Get element at key, insert new if non-existent
///
/// Complexity:
/// - Worst case: O(H * S + M)
/// - Best case: O(H)
///
/// \param k: The key of the element
/// \return The mapped value
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
