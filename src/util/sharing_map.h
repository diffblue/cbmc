/*******************************************************************\

Module: Sharing map

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Sharing map

#ifndef CPROVER_UTIL_SHARING_MAP_H
#define CPROVER_UTIL_SHARING_MAP_H

#ifdef SM_DEBUG
#include <iostream>
#endif

#include <functional>
#include <map>
#include <memory>
#include <set>
#include <stack>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <vector>

#include "as_const.h"
#include "irep.h"
#include "optional.h"
#include "sharing_node.h"
#include "threeval.h"

#ifdef SM_INTERNAL_CHECKS
#define SM_ASSERT(b) INVARIANT(b, "Sharing map internal invariant")
#else
#define SM_ASSERT(b)
#endif

// clang-format off

/// Macro to abbreviate the out-of-class definitions of methods and static
/// variables of sharing_mapt.
///
/// \param type the return type of the method or the type of the static variable
#define SHARING_MAPT(type) \
  template < \
    typename keyT, \
    typename valueT, \
    bool fail_if_equal, \
    typename hashT, \
    typename equalT> \
  type sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>

/// Macro to abbreviate the out-of-class definitions of methods of sharing_mapt
/// with a return type that is defined within the class.
///
/// \param cv_qualifiers the cv qualifiers of the return type of the method
/// \param return_type the return type of the method defined within sharing_mapt
#define SHARING_MAPT2(cv_qualifiers, return_type) \
  template < \
    typename keyT, \
    typename valueT, \
    bool fail_if_equal, \
    typename hashT, \
    typename equalT> \
  cv_qualifiers typename \
    sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>::return_type \
    sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>

/// Macro to abbreviate the out-of-class definitions of template methods of
/// sharing_mapt with a single template parameter and with a return type that is
/// defined within the class.
///
/// \param template_parameter name of the template parameter
/// \param cv_qualifiers the cv qualifiers of the return type of the method
/// \param return_type the return type of the method defined within sharing_mapt
#define SHARING_MAPT3(template_parameter, cv_qualifiers, return_type) \
  template < \
    typename keyT, \
    typename valueT, \
    bool fail_if_equal, \
    typename hashT, \
    typename equalT> \
  template <class template_parameter> \
  cv_qualifiers typename \
    sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>::return_type \
    sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>

/// Macro to abbreviate the out-of-class definitions of template methods of
/// sharing_mapt with a single template parameter.
///
/// \param template_parameter name of the template parameter
/// \param return_type the return type of the method
#define SHARING_MAPT4(template_parameter, return_type) \
  template < \
    typename keyT, \
    typename valueT, \
    bool fail_if_equal, \
    typename hashT, \
    typename equalT> \
  template <class template_parameter> \
  return_type sharing_mapt<keyT, valueT, fail_if_equal, hashT, equalT>
// clang-format on

/// A map implemented as a tree where subtrees can be shared between different
/// maps. The map is implemented as a variable-height n-ary trie.
///
/// When inserting a key-value pair into the map, first the hash of its key is
/// computed. The `bits` number of lower order bits of the hash are deemed
/// significant, and are grouped into `bits` / `chunk` chunks. The hash is then
/// treated as a string (with each chunk representing a character) for the
/// purposes of determining the position of the key-value pair in the trie. The
/// actual key-value pairs are stored in the leaf nodes. Collisions (i.e., two
/// different keys yield the same "string"), are handled by chaining the
/// corresponding key-value pairs in a `std::forward_list`.
///
/// The depth at which a key-value pair will be stored (when calling insert())
/// depends on the shortest unique prefix of its hash code (treated as a string)
/// with respect to the hash codes of the key-value pairs already in the map.
///
/// The use of a trie in combination with hashing has the advantage that the
/// tree is unlikely to degenerate (if the number of hash collisions is low).
/// This makes re-balancing operations unnecessary which do not interact well
/// with sharing. A disadvantage is that the height of the tree is likely
/// greater than if the elements had been stored in a balanced tree.
///
/// The nodes in the sharing map are objects of type sharing_nodet. A sharing
/// node has a shared pointer (of type small_shared_n_way_ptrt) which can point
/// to objects of type d_internalt, d_leaft, or d_containert (representing
/// internal nodes, leaf nodes, and container nodes, the latter being used for
/// chaining leafs in a linked list on hash collisions).
///
/// Sharing is initially generated when a map is assigned to another map or
/// copied via the copy constructor. Then both maps contain a pointer to the
/// root node of the tree that represents the maps. On subsequent modifications
/// to one of the maps, nodes are copied and sharing is lessened as described in
/// the following.
///
/// The replace(), update(), insert(), and erase() operations interact with
/// sharing as follows:
/// - When a key-value pair is inserted into the map (or a value of an existing
/// pair is replaced or updated) and its position is in a shared subtree,
/// already existing nodes from the root of the subtree to the position of the
/// key-value pair are copied and integrated with the map, and new nodes are
/// created as needed.
/// - When a key-value pair is erased from the map that is in a shared subtree,
/// nodes from the root of the subtree to the last node that will still exist on
/// the path to the erased element after the element has been removed are
/// copied and integrated with the map, and the remaining nodes are removed.
///
/// The replace() and update() operations are the only methods where sharing
/// could unnecessarily  be broken. This would happen when replacing an old
/// value with a new equal value, or calling update but making no change. The
/// sharing map provides a debug mode to detect such cases. When the template
/// parameter `fail_if_equal` is set to true, then the replace() and update()
/// methods yield an invariant violation when the new value is equal to the old
/// value.
/// For this to work, the type of the values stored in the map needs to have a
/// defined equality operator (operator==).
///
/// In the descriptions of the methods of the sharing map we also give the
/// complexity of the operations. We use the following symbols:
/// - N: number of key-value pairs in the map
/// - M: maximum number of key-value pairs that are chained in a leaf node
/// - H: maximum height of the tree
/// - S: maximum number of children per internal node
///
/// The first two symbols denote dynamic properties of a given map, whereas the
/// last two symbols are static configuration parameters of the map class.
template <
  typename keyT,
  typename valueT,
  bool fail_if_equal = false,
  typename hashT = std::hash<keyT>,
  typename equalT = std::equal_to<keyT>>
class sharing_mapt
{
public:
  ~sharing_mapt()
  {
  }

  typedef keyT key_type;
  typedef valueT mapped_type;

  typedef hashT hash;
  typedef equalT key_equal;

  typedef std::size_t size_type;

  typedef std::vector<key_type> keyst;

protected:
  typedef sharing_nodet<key_type, mapped_type> nodet;

  typedef typename nodet::to_mapt to_mapt;
  typedef typename nodet::leaf_listt leaf_listt;

  struct falset
  {
    bool operator()(const mapped_type &lhs, const mapped_type &rhs)
    {
      return false;
    }
  };

  typedef
    typename std::conditional<fail_if_equal, std::equal_to<valueT>, falset>::
      type value_equalt;

  struct noop_value_comparatort
  {
    explicit noop_value_comparatort(const mapped_type &)
    {
    }

    bool operator()(const mapped_type &)
    {
      return false;
    }
  };

  struct real_value_comparatort
  {
    mapped_type old_value;
    explicit real_value_comparatort(const mapped_type &old_value)
      : old_value(old_value)
    {
    }

    bool operator()(const mapped_type &new_value)
    {
      return old_value == new_value;
    }
  };

  typedef typename std::conditional<
    fail_if_equal,
    real_value_comparatort,
    noop_value_comparatort>::type value_comparatort;

public:
  // interface

  /// Erase element, element must exist in map
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(1)
  ///
  /// \param k: The key of the element to erase
  void erase(const key_type &k);

  /// Erase element if it exists
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(1)
  ///
  /// \param k: The key of the element to erase
  void erase_if_exists(const key_type &k)
  {
    if(has_key(k))
      erase(k);
  }

  /// Insert element, element must not exist in map
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(1)
  ///
  /// \param k: The key of the element to insert
  /// \param m: The mapped value to insert
  template <class valueU>
  void insert(const key_type &k, valueU &&m);

  /// Replace element, element must exist in map
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(1)
  ///
  /// \param k: The key of the element to insert
  /// \param m: The mapped value to replace the old value with
  template <class valueU>
  void replace(const key_type &k, valueU &&m);

  /// Update an element in place; element must exist in map
  ///
  /// Rationale: this avoids copy-out / edit / replace sequences without leaking
  ///   a non-const reference
  ///
  /// Complexity: as \ref sharing_mapt::replace
  ///
  /// \param k: The key of the element to update
  /// \param mutator: function to apply to the existing value. Must not store
  ///   the reference; should make some change to the stored value (if you are
  ///   unsure if you need to make a change, use \ref find beforehand)
  void update(const key_type &k, std::function<void(mapped_type &)> mutator);

  /// Find element
  ///
  /// Complexity:
  /// - Worst case: O(H * log(S) + M)
  /// - Best case: O(1)
  ///
  /// \param k: The key of the element to search
  /// \return optionalt containing a const reference to the value if found
  optionalt<std::reference_wrapper<const mapped_type>>
  find(const key_type &k) const;

  /// Swap with other map
  ///
  /// Complexity: O(1)
  void swap(sharing_mapt &other)
  {
    map.swap(other.map);

    std::size_t tmp = num;
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
  /// - Best case: O(1)
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
      const key_type &k,
      const mapped_type &m,
      const mapped_type &other_m)
      : k(k), m(m), other_m(&other_m)
    {
    }

    delta_view_itemt(const key_type &k, const mapped_type &m)
      : k(k), m(m), other_m(nullptr)
    {
    }

    const key_type &k;

    const mapped_type &m;

    bool is_in_both_maps() const
    {
      return other_m != nullptr;
    }

    const mapped_type &get_other_map_value() const
    {
      PRECONDITION(is_in_both_maps());
      return *other_m;
    }

  private:
    const mapped_type *other_m;
  };

  /// Delta view of the key-value pairs in two maps. A delta view of two maps is
  /// a view of the key-value pairs in the maps that are contained in subtrees
  /// that are not shared between them (also see get_delta_view()).
  typedef std::vector<delta_view_itemt> delta_viewt;

  /// Get a view of the elements in the map
  /// A view is a list of pairs with the components being const references to
  /// the keys and values in the map.
  ///
  /// Complexity:
  /// - Worst case: O(N * H * log(S))
  /// - Best case: O(N + H)
  ///
  /// \param [out] view: Empty view
  void get_view(viewt &view) const;

  /// Get a delta view of the elements in the map
  ///
  /// Informally, a delta view of two maps is a view of the key-value pairs in
  /// the maps that are contained in subtrees that are not shared between them.
  ///
  /// A delta view is represented as a list of structs, with each struct having
  /// three members (`key`, `value1`, `value2`). The elements `key`, `value1`,
  /// and `value2` are const references to the corresponding elements in the
  /// map, with the third being absent if the key only existed in the queried
  /// map. The first element is the key, the second element is the mapped value
  /// of the first map, and the third element is the mapped value of the second
  /// map if present.
  ///
  /// Calling `A.delta_view(B, ...)` yields a view such that for each element in
  /// the view one of two things holds:
  /// - the key is contained in both A and B, and in the maps the corresponding
  ///   key-value pairs are not contained in a subtree that is shared between
  ///   them
  /// - the key is only contained in A
  ///
  /// When `only_common=true`, the first case above holds for every element in
  /// the view.
  ///
  /// Complexity:
  /// - Worst case: O(max(N1, N2) * H * log(S) * M1 * M2) (no sharing)
  /// - Best case: O(1) (maximum sharing)
  ///
  /// The symbols N1, M1 refer to map A, and symbols N2, M2 refer to map B.
  ///
  /// \param other: other map
  /// \param [out] delta_view: Empty delta view
  /// \param only_common: Indicates if the returned delta view should only
  ///   contain key-value pairs for keys that exist in both maps
  void get_delta_view(
    const sharing_mapt &other,
    delta_viewt &delta_view,
    const bool only_common = true) const;

  /// Call a function for every key-value pair in the map.
  ///
  /// Complexity: as \ref sharing_mapt::get_view
  void
  iterate(std::function<void(const key_type &k, const mapped_type &m)> f) const
  {
    if(empty())
      return;

    iterate(map, f);
  }

#if !defined(_MSC_VER)
  /// Stats about sharing between several sharing map instances. An instance of
  /// this class is returned by the get_sharing_map_stats_* functions.
  ///
  /// The num_nodes field gives the total number of nodes in the given maps.
  /// Nodes that are part of n of the maps are counted n times.
  ///
  /// The num_unique_nodes field gives the number of unique nodes in the given
  /// maps. A node that is part of several of the maps is only counted once.
  ///
  /// The num_leafs and num_unique_leafs fields are similar to the above but
  /// only leafs are counted.
  struct sharing_map_statst
  {
    std::size_t num_nodes = 0;
    std::size_t num_unique_nodes = 0;
    std::size_t num_leafs = 0;
    std::size_t num_unique_leafs = 0;
  };

  /// Get sharing stats
  ///
  /// Complexity:
  /// - Worst case: O(N * H * log(S))
  /// - Best case: O(N + H)
  ///
  /// \param begin: begin iterator
  /// \param end: end iterator
  /// \param f: function applied to the iterator to get a sharing map
  /// \return sharing stats
  template <class Iterator>
  static sharing_map_statst get_sharing_stats(
    Iterator begin,
    Iterator end,
    std::function<sharing_mapt &(const Iterator)> f =
      [](const Iterator it) -> sharing_mapt & { return *it; });

  /// Get sharing stats
  ///
  /// Complexity:
  /// - Worst case: O(N * H * log(S))
  /// - Best case: O(N + H)
  ///
  /// \param begin: begin iterator of a map
  /// \param end: end iterator of a map
  /// \return sharing stats
  template <class Iterator>
  static sharing_map_statst get_sharing_stats_map(Iterator begin, Iterator end);
#endif

protected:
  // helpers

  nodet &get_leaf_node(const key_type &k);
  const nodet *get_leaf_node(const key_type &k) const;

  /// Move a leaf node further down the tree such as to resolve a collision with
  /// another key-value pair. This method is called by `insert()` to resolve a
  /// collision between a key-value pair to be newly inserted, and a key-value
  /// pair existing in the map.
  ///
  /// \param starting_level: the depth of the inner node pointing to the leaf
  ///   existing in the map
  /// \param key_suffix: hash code of the existing key in the map, shifted to
  ///   the right by `chunk * starting_level` bits (i.e., \p key_suffix is the
  ///   rest of the hash code used to determine the position of the key-value
  ///   pair below level \p starting_level
  /// \param bit_last: last portion of the hash code of the key existing in the
  ///   map (`inner[bit_last]` points to the leaf node to move further down the
  ///   tree)
  /// \param inner: inner node of which the child `inner[bit_last]` is the
  ///   leaf node to move further down the tree
  /// \param k: key of the element to be newly inserted
  /// \param m: value of the element to be newly inserted
  template <class valueU>
  void migrate(
    const std::size_t starting_level,
    const std::size_t key_suffix,
    const std::size_t bit_last,
    nodet &inner,
    const key_type &k,
    valueU &&m);

  void iterate(
    const nodet &n,
    std::function<void(const key_type &k, const mapped_type &m)> f) const;

  /// Add a delta item to the delta view if the value in the \p container (which
  /// must only contain a single leaf) is not shared with any of the values in
  /// the subtree below \p inner. This method is called by `get_delta_view()`
  /// when a container containing a single leaf is encountered in the first map,
  /// and the corresponding node in the second map is an inner node.
  ///
  /// \param leaf: leaf node which is part of the first map in a call
  ///   `map1.get_delta_view(map2, ...)`
  /// \param inner: inner node which is part of the second map
  /// \param level: depth of the nodes in the maps (both \p leaf and \p inner
  ///   must be at the same depth in their respective maps)
  /// \param delta_view: delta view to add delta items to
  /// \param only_common: flag indicating if only items are added to the delta
  ///   view for which the keys are in both maps
  void add_item_if_not_shared(
    const nodet &leaf,
    const nodet &inner,
    const std::size_t level,
    delta_viewt &delta_view,
    const bool only_common) const;

  void gather_all(const nodet &n, delta_viewt &delta_view) const;

  std::size_t count_unmarked_nodes(
    bool leafs_only,
    std::set<const void *> &marked,
    bool mark = true) const;

  static const std::size_t dummy_level;

  // config
  static const std::size_t bits;
  static const std::size_t chunk;

  // derived config
  static const std::size_t mask;
  static const std::size_t levels;

  // key-value map
  nodet map;

  // number of elements in the map
  size_type num = 0;
};

SHARING_MAPT(void)
::iterate(
  const nodet &n,
  std::function<void(const key_type &k, const mapped_type &m)> f) const
{
  SM_ASSERT(!n.empty());

  std::stack<const nodet *> stack;
  stack.push(&n);

  do
  {
    const nodet *ip = stack.top();
    stack.pop();

    SM_ASSERT(!ip->empty());

    if(ip->is_internal())
    {
      const to_mapt &m = ip->get_to_map();
      SM_ASSERT(!m.empty());

      for(const auto &item : m)
      {
        stack.push(&item.second);
      }
    }
    else if(ip->is_leaf())
    {
      f(ip->get_key(), ip->get_value());
    }
    else
    {
      SM_ASSERT(ip->is_defined_container());

      const leaf_listt &ll = ip->get_container();
      SM_ASSERT(!ll.empty());

      for(const auto &l : ll)
      {
        f(l.get_key(), l.get_value());
      }
    }
  }
  while(!stack.empty());
}

SHARING_MAPT(std::size_t)
::count_unmarked_nodes(
  bool leafs_only,
  std::set<const void *> &marked,
  bool mark) const
{
  if(empty())
    return 0;

  unsigned count = 0;

  std::stack<const nodet *> stack;
  stack.push(&map);

  do
  {
    const nodet *ip = stack.top();
    SM_ASSERT(!ip->empty());
    stack.pop();

    const unsigned use_count = ip->use_count();

    const void *raw_ptr =
      ip->is_internal() ? (const void *)&ip->read_internal()
                        : ip->is_leaf() ? (const void *)&ip->read_leaf()
                                        : (const void *)&ip->read_container();

    if(use_count >= 2)
    {
      if(marked.find(raw_ptr) != marked.end())
      {
        continue;
      }

      if(mark)
      {
        marked.insert(raw_ptr);
      }
    }

    if(ip->is_internal())
    {
      if(!leafs_only)
      {
        count++;
      }

      const to_mapt &m = ip->get_to_map();
      SM_ASSERT(!m.empty());

      for(const auto &item : m)
      {
        stack.push(&item.second);
      }
    }
    else if(ip->is_leaf())
    {
      count++;
    }
    else
    {
      SM_ASSERT(ip->is_defined_container());

      if(!leafs_only)
      {
        count++;
      }

      const leaf_listt &ll = ip->get_container();
      SM_ASSERT(!ll.empty());

      for(const auto &l : ll)
      {
        stack.push(&l);
      }
    }
  } while(!stack.empty());

  return count;
}

#if !defined(_MSC_VER)
SHARING_MAPT3(Iterator, , sharing_map_statst)
::get_sharing_stats(
  Iterator begin,
  Iterator end,
  std::function<sharing_mapt &(const Iterator)> f)
{
  std::set<const void *> marked;
  sharing_map_statst sms;

  // We do a separate pass over the tree for each statistic. This is not very
  // efficient but the function is intended only for diagnosis purposes anyways.

  // number of nodes
  for(Iterator it = begin; it != end; it++)
  {
    sms.num_nodes += f(it).count_unmarked_nodes(false, marked, false);
  }

  SM_ASSERT(marked.empty());

  // number of unique nodes
  for(Iterator it = begin; it != end; it++)
  {
    sms.num_unique_nodes += f(it).count_unmarked_nodes(false, marked, true);
  }

  marked.clear();

  // number of leafs
  for(Iterator it = begin; it != end; it++)
  {
    sms.num_leafs += f(it).count_unmarked_nodes(true, marked, false);
  }

  SM_ASSERT(marked.empty());

  // number of unique leafs
  for(Iterator it = begin; it != end; it++)
  {
    sms.num_unique_leafs += f(it).count_unmarked_nodes(true, marked, true);
  }

  return sms;
}

SHARING_MAPT3(Iterator, , sharing_map_statst)
::get_sharing_stats_map(Iterator begin, Iterator end)
{
  return get_sharing_stats<Iterator>(
    begin, end, [](const Iterator it) -> sharing_mapt & { return it->second; });
}
#endif

SHARING_MAPT(void)::get_view(viewt &view) const
{
  SM_ASSERT(view.empty());

  if(empty())
    return;

  auto f = [&view](const key_type &k, const mapped_type &m) {
    view.push_back(view_itemt(k, m));
  };

  iterate(map, f);
}

SHARING_MAPT(void)
::gather_all(const nodet &n, delta_viewt &delta_view) const
{
  auto f = [&delta_view](const key_type &k, const mapped_type &m) {
    delta_view.push_back(delta_view_itemt(k, m));
  };

  iterate(n, f);
}

SHARING_MAPT(void)::add_item_if_not_shared(
  const nodet &leaf,
  const nodet &inner,
  const std::size_t level,
  delta_viewt &delta_view,
  const bool only_common) const
{
  const auto &k = leaf.get_key();
  std::size_t key = hash()(k);

  key >>= level * chunk;

  const nodet *ip = &inner;
  SM_ASSERT(ip->is_defined_internal());

  while(true)
  {
    std::size_t bit = key & mask;

    ip = ip->find_child(bit);

    // only in first map
    if(ip == nullptr)
    {
      if(!only_common)
      {
        delta_view.push_back({k, leaf.get_value()});
      }

      return;
    }

    SM_ASSERT(!ip->empty());

    // potentially in both maps
    if(ip->is_container())
    {
      for(const auto &l2 : ip->get_container())
      {
        if(leaf.shares_with(l2))
          return;

        if(leaf.get_key() == l2.get_key())
        {
          delta_view.push_back({k, leaf.get_value(), l2.get_value()});
          return;
        }
      }

      delta_view.push_back({k, leaf.get_value()});

      return;
    }

    if(ip->is_leaf())
    {
      if(ip->shares_with(leaf))
        return;

      if(equalT()(leaf.get_key(), ip->get_key()))
      {
        delta_view.push_back({k, leaf.get_value(), ip->get_value()});
        return;
      }

      delta_view.push_back({k, leaf.get_value()});

      return;
    }

    key >>= chunk;
  }
}

SHARING_MAPT(void)
::get_delta_view(
  const sharing_mapt &other,
  delta_viewt &delta_view,
  const bool only_common) const
{
  SM_ASSERT(delta_view.empty());

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

  typedef std::pair<const nodet *, const nodet *> stack_itemt;
  std::stack<stack_itemt> stack;

  std::stack<std::size_t> level_stack;

  // We do a DFS "in lockstep" simultaneously on both maps. For
  // corresponding nodes we check whether they are shared between the
  // maps, and if not, we recurse into the corresponding subtrees.

  // The stack contains the children of already visited nodes that we
  // still have to visit during the traversal.

  if(map.shares_with(other.map))
    return;

  stack.push(stack_itemt(&map, &other.map));
  level_stack.push(0);

  do
  {
    const stack_itemt &si = stack.top();

    const nodet *ip1 = si.first;
    const nodet *ip2 = si.second;

    SM_ASSERT(!ip1->shares_with(*ip2));

    stack.pop();

    const std::size_t level = level_stack.top();
    level_stack.pop();

    SM_ASSERT(!ip1->empty());
    SM_ASSERT(!ip2->empty());

    if(ip1->is_internal())
    {
      SM_ASSERT(!ip2->is_container());

      if(ip2->is_internal())
      {
        for(const auto &item : ip1->get_to_map())
        {
          const nodet &child = item.second;

          const nodet *p;
          p = ip2->find_child(item.first);

          if(p == nullptr)
          {
            if(!only_common)
            {
              gather_all(child, delta_view);
            }
          }
          else if(!child.shares_with(*p))
          {
            stack.push(stack_itemt(&child, p));
            level_stack.push(level + 1);
          }
        }
      }
      else
      {
        SM_ASSERT(ip2->is_leaf());

        for(const auto &item : ip1->get_to_map())
        {
          const nodet &child = item.second;

          if(!child.shares_with(*ip2))
          {
            stack.push(stack_itemt(&child, ip2));

            // The level is not needed when the node of the left map is an
            // internal node, and the node of the right map is a leaf node,
            // hence we just push a dummy element
            level_stack.push(dummy_level);
          }
        }
      }
    }
    else if(ip1->is_leaf())
    {
      SM_ASSERT(!ip2->is_container());

      if(ip2->is_internal())
      {
        SM_ASSERT(level != dummy_level);

        add_item_if_not_shared(*ip1, *ip2, level, delta_view, only_common);
      }
      else
      {
        SM_ASSERT(ip2->is_leaf());

        if(equalT()(ip1->get_key(), ip2->get_key()))
        {
          delta_view.push_back(
            {ip1->get_key(), ip1->get_value(), ip2->get_value()});
        }
        else if(!only_common)
        {
          delta_view.push_back({ip1->get_key(), ip1->get_value()});
        }
      }
    }
    else
    {
      SM_ASSERT(ip1->is_container());
      SM_ASSERT(!ip2->is_internal());

      if(ip2->is_leaf())
      {
        for(const auto &l1 : ip1->get_container())
        {
          if(l1.shares_with(*ip2))
          {
            continue;
          }

          const key_type &k1 = l1.get_key();

          if(equalT()(k1, ip2->get_key()))
          {
            delta_view.push_back({k1, l1.get_value(), ip2->get_value()});
          }
          else if(!only_common)
          {
            delta_view.push_back({k1, l1.get_value()});
          }
        }
      }
      else
      {
        SM_ASSERT(ip2->is_container());

        for(const auto &l1 : ip1->get_container())
        {
          const key_type &k1 = l1.get_key();
          const nodet *p;

          p = ip2->find_leaf(k1);

          if(p != nullptr)
          {
            if(!l1.shares_with(*p))
            {
              SM_ASSERT(other.has_key(k1));
              delta_view.push_back({k1, l1.get_value(), p->get_value()});
            }
          }
          else if(!only_common)
          {
            SM_ASSERT(!other.has_key(k1));
            delta_view.push_back({k1, l1.get_value()});
          }
        }
      }
    }
  }
  while(!stack.empty());
}

SHARING_MAPT2(, nodet &)::get_leaf_node(const key_type &k)
{
  SM_ASSERT(has_key(k));

  std::size_t key = hash()(k);
  nodet *ip = &map;
  SM_ASSERT(ip->is_defined_internal());

  while(true)
  {
    std::size_t bit = key & mask;

    ip = &ip->add_child(bit);
    PRECONDITION(!ip->empty()); // since the key must exist in the map

    if(ip->is_internal())
    {
      key >>= chunk;
      continue;
    }
    else if(ip->is_leaf())
    {
      return *ip;
    }
    else
    {
      SM_ASSERT(ip->is_defined_container());
      return *ip->find_leaf(k);
    }
  }
}

SHARING_MAPT2(const, nodet *)::get_leaf_node(const key_type &k) const
{
  if(empty())
    return nullptr;

  std::size_t key = hash()(k);
  const nodet *ip = &map;
  SM_ASSERT(ip->is_defined_internal());

  while(true)
  {
    std::size_t bit = key & mask;

    ip = ip->find_child(bit);

    if(ip == nullptr)
      return nullptr;

    SM_ASSERT(!ip->empty());

    if(ip->is_internal())
    {
      key >>= chunk;
      continue;
    }
    else if(ip->is_leaf())
    {
      return equalT()(ip->get_key(), k) ? ip : nullptr;
    }
    else
    {
      SM_ASSERT(ip->is_defined_container());
      return ip->find_leaf(k); // returns nullptr if leaf is not found
    }
  }

  UNREACHABLE;
  return nullptr;
}

SHARING_MAPT(void)::erase(const key_type &k)
{
  SM_ASSERT(has_key(k));

  nodet *del = nullptr;
  std::size_t del_bit = 0;

  std::size_t key = hash()(k);
  nodet *ip = &map;

  while(true)
  {
    std::size_t bit = key & mask;

    const to_mapt &m = as_const_ptr(ip)->get_to_map();

    if(m.size() > 1 || del == nullptr)
    {
      del = ip;
      del_bit=bit;
    }

    ip = &ip->add_child(bit);

    PRECONDITION(!ip->empty());

    if(ip->is_internal())
    {
      key >>= chunk;
      continue;
    }
    else if(ip->is_leaf())
    {
      PRECONDITION(equalT()(ip->get_key(), k));
      del->remove_child(del_bit);

      num--;

      return;
    }
    else
    {
      SM_ASSERT(ip->is_defined_container());
      const leaf_listt &ll = as_const_ptr(ip)->get_container();
      PRECONDITION(!ll.empty());

      // forward list has one element
      if(std::next(ll.begin()) == ll.end())
      {
        PRECONDITION(equalT()(ll.front().get_key(), k));
        del->remove_child(del_bit);
      }
      else
      {
        ip->remove_leaf(k);
      }

      num--;

      return;
    }
  }

  UNREACHABLE;
}

SHARING_MAPT4(valueU, void)
::migrate(
  const std::size_t starting_level,
  const std::size_t key_suffix,
  const std::size_t bit_last,
  nodet &inner,
  const key_type &k,
  valueU &&m)
{
  SM_ASSERT(starting_level < levels - 1);
  SM_ASSERT(inner.is_defined_internal());

  nodet &leaf = inner.add_child(bit_last);
  SM_ASSERT(leaf.is_defined_leaf());

  std::size_t key_existing = hash()(leaf.get_key());
  key_existing >>= chunk * starting_level;

  nodet leaf_kept;
  leaf_kept.swap(leaf);

  nodet *ip = &leaf;
  SM_ASSERT(ip->empty());

  // Find place for both elements

  std::size_t level = starting_level + 1;
  std::size_t key = key_suffix;

  key_existing >>= chunk;
  key >>= chunk;

  SM_ASSERT(level < levels);

  do
  {
    SM_ASSERT(ip->empty());

    std::size_t bit_existing = key_existing & mask;
    std::size_t bit = key & mask;

    if(bit != bit_existing)
    {
      // Place found

      nodet &l1 = ip->add_child(bit_existing);
      SM_ASSERT(l1.empty());
      l1.swap(leaf_kept);

      nodet &l2 = ip->add_child(bit);
      SM_ASSERT(l2.empty());
      l2.make_leaf(k, std::forward<valueU>(m));

      return;
    }

    SM_ASSERT(bit == bit_existing);
    ip = &ip->add_child(bit);

    key >>= chunk;
    key_existing >>= chunk;

    level++;
  } while(level < levels);

  // Hash collision, create container and add both elements to it

  PRECONDITION(!equalT()(k, leaf_kept.get_key()));

  SM_ASSERT(ip->empty());
  // Make container and add existing leaf
  ip->get_container().push_front(leaf_kept);

  SM_ASSERT(ip->is_defined_container());
  // Insert new element in same container
  ip->place_leaf(k, std::forward<valueU>(m));
}

SHARING_MAPT4(valueU, void)
::insert(const key_type &k, valueU &&m)
{
  SM_ASSERT(!has_key(k));

  std::size_t key = hash()(k);
  nodet *ip = &map;

  // The root must be an internal node
  SM_ASSERT(ip->is_internal());

  std::size_t level = 0;

  while(true)
  {
    std::size_t bit = key & mask;

    SM_ASSERT(ip != nullptr);
    SM_ASSERT(ip->is_internal());
    SM_ASSERT(level == 0 || !ip->empty());

    nodet &child = ip->add_child(bit);

    // Place is unoccupied
    if(child.empty())
    {
      if(level < levels - 1)
      {
        // Create leaf
        child.make_leaf(k, m);
      }
      else
      {
        SM_ASSERT(level == levels - 1);

        // Create container and insert leaf
        child.place_leaf(k, std::forward<valueU>(m));

        SM_ASSERT(child.is_defined_container());
      }

      num++;

      return;
    }
    else if(child.is_internal())
    {
      ip = &child;
      key >>= chunk;
      level++;

      continue;
    }
    else if(child.is_leaf())
    {
      // migrate leaf downwards
      migrate(level, key, bit, *ip, k, std::forward<valueU>(m));

      num++;

      return;
    }
    else
    {
      SM_ASSERT(child.is_defined_container());
      SM_ASSERT(level == levels - 1);

      // Add to the container
      child.place_leaf(k, std::forward<valueU>(m));

      num++;

      return;
    }
  }
}

SHARING_MAPT4(valueU, void)
::replace(const key_type &k, valueU &&m)
{
  nodet &lp = get_leaf_node(k);

  INVARIANT(
    !value_equalt()(lp.get_value(), m),
    "values should not be replaced with equal values to maximize sharing");

  lp.set_value(std::forward<valueU>(m));
}

SHARING_MAPT(void)
::update(const key_type &k, std::function<void(mapped_type &)> mutator)
{
  nodet &lp = get_leaf_node(k);

  value_comparatort comparator(lp.get_value());

  lp.mutate_value(mutator);

  INVARIANT(
    !comparator(lp.get_value()),
    "sharing_mapt::update should make some change. Consider using read-only "
    "method to check if an update is needed beforehand");
}

SHARING_MAPT2(optionalt<std::reference_wrapper<const, mapped_type>>)::find(
  const key_type &k) const
{
  const nodet *lp = get_leaf_node(k);

  if(lp == nullptr)
    return {};

  return optionalt<std::reference_wrapper<const mapped_type>>(lp->get_value());
}

// static constants

SHARING_MAPT(const std::size_t)::dummy_level = 0xff;

SHARING_MAPT(const std::size_t)::bits = 30;
SHARING_MAPT(const std::size_t)::chunk = 3;

SHARING_MAPT(const std::size_t)::mask = 0xffff >> (16 - chunk);
SHARING_MAPT(const std::size_t)::levels = bits / chunk;

#endif
