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
/// corresponding key-value pairs in a `std::forward_list`.
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
/// The replace(), insert(), and erase() operations interact with sharing as
/// follows:
/// - When a key-value pair is inserted into the map (or a value of an existing
/// pair is replaced) and its position is in a shared subtree, already existing
/// nodes from the root of the subtree to the position of the key-value pair are
/// copied and integrated with the map, and new nodes are created as needed.
/// - When a key-value pair is erased from the map that is in a shared subtree,
/// nodes from the root of the subtree to the last node that will still exist on
/// the path to the erased element after the element has been removed are
/// copied and integrated with the map, and the remaining nodes are removed.
///
/// The replace() operation is the only method where sharing could unnecessarily
/// be broken. This would happen when replacing an old value with a new equal
/// value. The sharing map provides a debug mode to detect such cases. When the
/// template parameter `fail_if_equal` is set to true, then the replace() method
/// yields an invariant violation when the new value is equal to the old value.
/// For this to work, the type of the values stored in the map needs to have a
/// defined equality operator (operator==).
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
  typedef sharing_node_innert<key_type, mapped_type> innert;
  typedef sharing_node_leaft<key_type, mapped_type> leaft;

  typedef sharing_node_baset baset;

  typedef typename innert::to_mapt to_mapt;
  typedef typename innert::leaf_listt leaf_listt;

  struct truet
  {
    bool operator()(const mapped_type &lhs, const mapped_type &rhs)
    {
      return true;
    }
  };

  typedef
    typename std::conditional<fail_if_equal, std::equal_to<valueT>, truet>::type
      value_equalt;

public:
  // interface

  /// Erase element
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(H)
  ///
  /// \param k: The key of the element to erase
  /// \param key_exists: Hint to indicate whether the element is known to exist
  ///   (possible values `unknown` or` true`)
  size_type erase(const key_type &k, const tvt &key_exists = tvt::unknown());

  /// Erase all elements
  ///
  /// Complexity:
  /// - Worst case: O(K * (H * S + M))
  /// - Best case: O(K * H)
  ///
  /// \param ks: The keys of the element to erase
  /// \param key_exists: Hint to indicate whether the elements are known to
  ///   exist (possible values `unknown` or `true`). Applies to all elements
  ///   (i.e., have to use `unknown` if for at least one element it is not known
  ///   whether it exists)
  size_type erase_all(
    const keyst &ks,
    const tvt &key_exists = tvt::unknown()); // applies to all keys

  /// Insert element, element must not exist in map
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(H)
  ///
  /// \param k: The key of the element to insert
  /// \param m: The mapped value to insert
  template <class valueU>
  void insert(const key_type &k, valueU &&m);

  /// Replace element, element must exist in map
  ///
  /// Complexity:
  /// - Worst case: O(H * S + M)
  /// - Best case: O(H)
  ///
  /// \param k: The key of the element to insert
  /// \param m: The mapped value to replace the old value with
  template <class valueU>
  void replace(const key_type &k, valueU &&m);
  /// Find element
  ///
  /// Complexity:
  /// - Worst case: O(H * log(S) + M)
  /// - Best case: O(H)
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
  /// four members (`in_both`, `key`, `value1`, `value2`). The elements `key`,
  /// `value1`, and `value2` are const references to the corresponding elements
  /// in the map. The first element indicates whether the key exists in both
  /// maps, the second element is the key, the third element is the mapped value
  /// of the first map, and the fourth element is the mapped value of the second
  /// map, or a dummy element if the key exists only in the first map (in which
  /// case `in_both` is false).
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

  innert *get_container_node(const key_type &k);
  const innert *get_container_node(const key_type &k) const;

  const leaft *get_leaf_node(const key_type &k) const
  {
    const innert *cp = get_container_node(k);
    if(cp == nullptr)
      return nullptr;

    const leaft *lp;
    lp = cp->find_leaf(k);

    return lp;
  }

  void iterate(
    const baset &n,
    const unsigned start_depth,
    std::function<void(const key_type &k, const mapped_type &m)> f) const;

  void gather_all(const baset &n, const unsigned depth, delta_viewt &delta_view)
    const;

  std::size_t count_unmarked_nodes(
    bool leafs_only,
    std::set<const void *> &marked,
    bool mark = true) const;

  // dummy element returned when no element was found
  static mapped_type dummy;

  static const std::string not_found_msg;

  // config
  static const std::size_t bits;
  static const std::size_t chunk;

  // derived config
  static const std::size_t mask;
  static const std::size_t steps;

  // key-value map
  innert map;

  // number of elements in the map
  size_type num = 0;
};

SHARING_MAPT(void)
::iterate(
  const baset &n,
  unsigned start_depth,
  std::function<void(const key_type &k, const mapped_type &m)> f) const
{
  typedef std::pair<unsigned, const baset *> stack_itemt;

  std::stack<stack_itemt> stack;
  stack.push({start_depth, &n});

  do
  {
    const stack_itemt &si = stack.top();

    const unsigned depth = si.first;
    const baset *bp = si.second;

    stack.pop();

    if(depth < steps) // internal
    {
      const innert *ip = static_cast<const innert *>(bp);
      const to_mapt &m = ip->get_to_map();
      SM_ASSERT(!m.empty());

      for(const auto &item : m)
      {
        const innert *i = &item.second;
        stack.push({depth + 1, i});
      }
    }
    else // container
    {
      SM_ASSERT(depth == steps);

      const innert *cp = static_cast<const innert *>(bp);
      const leaf_listt &ll = cp->get_container();
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

  // depth, node pointer
  typedef std::pair<unsigned, const baset *> stack_itemt;

  std::stack<stack_itemt> stack;
  stack.push({0, &map});

  do
  {
    const stack_itemt &si = stack.top();

    const unsigned depth = si.first;
    const baset *bp = si.second;

    stack.pop();

    // internal node or container node
    const innert *ip = static_cast<const innert *>(bp);
    const unsigned use_count = ip->use_count();
    const void *raw_ptr = ip->is_internal()
                            ? (const void *)&ip->read_internal()
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

    if(!leafs_only)
    {
      count++;
    }

    if(depth < steps) // internal
    {
      const to_mapt &m = ip->get_to_map();
      SM_ASSERT(!m.empty());

      for(const auto &item : m)
      {
        const innert *i = &item.second;
        stack.push({depth + 1, i});
      }
    }
    else // container
    {
      SM_ASSERT(depth == steps);

      const leaf_listt &ll = ip->get_container();
      SM_ASSERT(!ll.empty());

      for(const auto &l : ll)
      {
        const unsigned leaf_use_count = l.use_count();
        const void *leaf_raw_ptr = &l.read();

        if(leaf_use_count >= 2)
        {
          if(marked.find(leaf_raw_ptr) != marked.end())
          {
            continue;
          }

          if(mark)
          {
            marked.insert(leaf_raw_ptr);
          }
        }

        count++;
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

  iterate(map, 0, f);
}

SHARING_MAPT(void)
::gather_all(const baset &n, unsigned depth, delta_viewt &delta_view) const
{
  auto f = [&delta_view](const key_type &k, const mapped_type &m) {
    delta_view.push_back(delta_view_itemt(false, k, m, dummy));
  };

  iterate(n, depth, f);
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
      gather_all(map, 0, delta_view);
    }

    return;
  }

  typedef std::tuple<unsigned, const baset *, const baset *> stack_itemt;
  std::stack<stack_itemt> stack;

  // We do a DFS "in lockstep" simultaneously on both maps. For
  // corresponding nodes we check whether they are shared between the
  // maps, and if not, we recurse into the corresponding subtrees.

  // The stack contains the children of already visited nodes that we
  // still have to visit during the traversal.

  stack.push(stack_itemt(0, &map, &other.map));

  do
  {
    const stack_itemt &si = stack.top();

    const unsigned depth = std::get<0>(si);
    const baset *bp1 = std::get<1>(si);
    const baset *bp2 = std::get<2>(si);

    stack.pop();

    if(depth < steps) // internal
    {
      const innert *ip1 = static_cast<const innert *>(bp1);
      const innert *ip2 = static_cast<const innert *>(bp2);

      const to_mapt &m = ip1->get_to_map();

      for(const auto &item : m)
      {
        const innert *p;

        p = ip2->find_child(item.first);
        if(p==nullptr)
        {
          if(!only_common)
          {
            gather_all(item.second, depth + 1, delta_view);
          }
        }
        else if(!item.second.shares_with(*p))
        {
          stack.push(stack_itemt(depth + 1, &item.second, p));
        }
      }
    }
    else // container
    {
      SM_ASSERT(depth == steps);

      const innert *cp1 = static_cast<const innert *>(bp1);
      const innert *cp2 = static_cast<const innert *>(bp2);

      const leaf_listt &ll1 = cp1->get_container();

      for(const auto &l1 : ll1)
      {
        const key_type &k1=l1.get_key();
        const leaft *p;

        p = cp2->find_leaf(k1);

        if(p != nullptr)
        {
          if(!l1.shares_with(*p))
          {
            delta_view.push_back({true, k1, l1.get_value(), p->get_value()});
          }
        }
        else if(!only_common)
        {
          delta_view.push_back({false, l1.get_key(), l1.get_value(), dummy});
        }
      }
    }
  }
  while(!stack.empty());
}

SHARING_MAPT2(, innert *)::get_container_node(const key_type &k)
{
  std::size_t key = hash()(k);
  innert *ip = &map;

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;

    ip = ip->add_child(bit);

    key >>= chunk;
  }

  return ip;
}

SHARING_MAPT2(const, innert *)::get_container_node(const key_type &k) const
{
  if(empty())
    return nullptr;

  std::size_t key = hash()(k);
  const innert *ip = &map;

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;

    ip = ip->find_child(bit);
    if(ip == nullptr)
      return nullptr;

    key >>= chunk;
  }

  return ip;
}

SHARING_MAPT2(, size_type)::erase(const key_type &k, const tvt &key_exists)
{
  SM_ASSERT(!key_exists.is_false());
  SM_ASSERT(!key_exists.is_true() || has_key(k));

  // check if key exists
  if(key_exists.is_unknown() && !has_key(k))
    return 0;

  innert *del = nullptr;
  std::size_t del_bit = 0;
  std::size_t del_level = 0;

  std::size_t key = hash()(k);
  innert *ip = &map;

  for(std::size_t i = 0; i < steps; i++)
  {
    std::size_t bit = key & mask;

    const to_mapt &m = as_const(ip)->get_to_map();

    if(m.size() > 1 || del == nullptr)
    {
      del = ip;
      del_bit=bit;
      del_level = i;
    }

    ip = ip->add_child(bit);

    key >>= chunk;
  }

  const leaf_listt &ll = as_const(ip)->get_container();

  // forward list has one element
  if(!ll.empty() && std::next(ll.begin()) == ll.end())
  {
    if(del_level < steps - 1)
    {
      del->remove_child(del_bit);
    }
    else
    {
      SM_ASSERT(del_level == steps - 1);
      del->remove_child(del_bit);
    }

    num--;
    return 1;
  }

  SM_ASSERT(!ll.empty());

  ip->remove_leaf(k);
  num--;

  return 1;
}

SHARING_MAPT2(, size_type)
::erase_all(const keyst &ks, const tvt &key_exists)
{
  size_type cnt = 0;

  for(const key_type &k : ks)
  {
    cnt+=erase(k, key_exists);
  }

  return cnt;
}

SHARING_MAPT4(valueU, void)
::insert(const key_type &k, valueU &&m)
{
  innert *cp = get_container_node(k);
  SM_ASSERT(cp != nullptr);

  cp->place_leaf(k, std::forward<valueU>(m));
  num++;
}

SHARING_MAPT4(valueU, void)
::replace(const key_type &k, valueU &&m)
{
  innert *cp = get_container_node(k);
  SM_ASSERT(cp != nullptr);

  leaft *lp = cp->find_leaf(k);
  PRECONDITION(lp != nullptr); // key must exist in map

  INVARIANT(
    value_equalt()(as_const(lp)->get_value(), m),
    "values should not be replaced with equal values to maximize sharing");

  lp->set_value(std::forward<valueU>(m));
}

SHARING_MAPT2(optionalt<std::reference_wrapper<const, mapped_type>>)::find(
  const key_type &k) const
{
  const leaft *lp = get_leaf_node(k);

  if(lp == nullptr)
    return {};

  return optionalt<std::reference_wrapper<const mapped_type>>(lp->get_value());
}

// static constants

SHARING_MAPT(const std::string)::not_found_msg="key not found";

SHARING_MAPT2(, mapped_type)::dummy;

SHARING_MAPT(const std::size_t)::bits = 18;
SHARING_MAPT(const std::size_t)::chunk = 3;

SHARING_MAPT(const std::size_t)::mask = 0xffff >> (16 - chunk);
SHARING_MAPT(const std::size_t)::steps = bits / chunk;

#endif
