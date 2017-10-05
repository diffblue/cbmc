/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UNION_FIND_H
#define CPROVER_UTIL_UNION_FIND_H

#include <cassert>
#include <vector>

#include "numbering.h"

// Standard union find with weighting and path compression.
// See http://www.cs.princeton.edu/~rs/AlgsDS07/01UnionFind.pdf

// NOLINTNEXTLINE(readability/identifiers)
class unsigned_union_find
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  using size_type = std::size_t;

protected:
  struct nodet
  {
    size_type count; // set size
    size_type parent;

    // constructs a root node
    explicit nodet(size_type index):count(1), parent(index)
    {
    }
  };

  // This is mutable to allow path compression in find().
  mutable std::vector<nodet> nodes;

public:
  // merge the sets 'a' and 'b'
  void make_union(size_type a, size_type b);

  // find the root of the set 'a' belongs to
  size_type find(size_type a) const;

  // Makes 'this' the union-find with the following:
  // any union in 'this' will be present in both source sets,
  // i.e., this is the strongest implication of the two
  // data structures.
  void intersection(const unsigned_union_find &other);

  // remove from any sets
  void isolate(size_type a);

  void swap(unsigned_union_find &other)
  {
    other.nodes.swap(nodes);
  }

  void resize(size_type size)
  {
    // We only enlarge. Shrinking is yet to be implemented.
    assert(nodes.size()<=size);
    nodes.reserve(size);
    while(nodes.size()<size)
      nodes.push_back(nodet(nodes.size()));
  }

  void clear()
  {
    nodes.clear();
  }

  // is 'a' a root?
  bool is_root(size_type a) const
  {
    if(a>=size())
      return true;
    // a root is its own parent
    return nodes[a].parent==a;
  }

  // are 'a' and 'b' in the same set?
  bool same_set(size_type a, size_type b) const
  {
    return find(a)==find(b);
  }

  // total number of elements
  size_type size() const
  {
    return nodes.size();
  }

  // size of the set that 'a' is in
  size_type count(size_type a) const
  {
    if(a>=size())
      return 1;
    return nodes[find(a)].count;
  }

  // make the array large enough to contain 'a'
  void check_index(size_type a)
  {
    if(a>=size())
      resize(a+1);
  }

  // number of disjoint sets
  size_type count_roots() const
  {
    size_type c=0;
    for(size_type i=0; i<nodes.size(); i++)
      if(is_root(i))
        c++;
    return c;
  }

  // makes 'new_root' the root of the set 'old'
  void re_root(size_type old, size_type new_root);

  // find a different member of the same set
  size_type get_other(size_type a);
};

template <typename T>
// NOLINTNEXTLINE(readability/identifiers)
class union_find final
{
  using numbering_typet = numbering<T>;
  numbering_typet numbers;

  // NOLINTNEXTLINE(readability/identifiers)
  using number_type = typename numbering_typet::number_type;

public:
  // NOLINTNEXTLINE(readability/identifiers)
  using size_type = typename numbering_typet::size_type;
  // NOLINTNEXTLINE(readability/identifiers)
  using iterator = typename numbering_typet::iterator;
  // NOLINTNEXTLINE(readability/identifiers)
  using const_iterator = typename numbering_typet::const_iterator;

  // true == already in same set
  bool make_union(const T &a, const T &b)
  {
    size_type na=number(a), nb=number(b);
    bool is_union=find_number(na)==find_number(nb);
    uuf.make_union(na, nb);
    return is_union;
  }

  // true == already in same set
  bool make_union(typename numbering<T>::const_iterator it_a,
                  typename numbering<T>::const_iterator it_b)
  {
    size_type na=it_a-numbers.begin(), nb=it_b-numbers.begin();
    bool is_union=find_number(na)==find_number(nb);
    uuf.make_union(na, nb);
    return is_union;
  }

  // are 'a' and 'b' in the same set?
  bool same_set(const T &a, const T &b) const
  {
    number_type na, nb;
    bool have_na=!numbers.get_number(a, na),
         have_nb=!numbers.get_number(b, nb);

    if(have_na && have_nb)
      return uuf.same_set(na, nb);
    else if(!have_na && !have_nb)
      return a==b;
    else
      return false;
  }

  // are 'a' and 'b' in the same set?
  bool same_set(typename numbering<T>::const_iterator it_a,
                typename numbering<T>::const_iterator it_b) const
  {
    return uuf.same_set(it_a-numbers.begin(), it_b-numbers.begin());
  }

  const T &find(typename numbering<T>::const_iterator it) const
  {
    return numbers[find_number(it-numbers.begin())];
  }

  const T &find(const T &a)
  {
    return numbers[find_number(number(a))];
  }

  size_type find_number(typename numbering<T>::const_iterator it) const
  {
    return find_number(it-numbers.begin());
  }

  size_type find_number(size_type a) const
  {
    return uuf.find(a);
  }

  size_type find_number(const T &a)
  {
    return uuf.find(number(a));
  }

  bool is_root_number(size_type a) const
  {
    return uuf.is_root(a);
  }

  bool is_root(const T &a) const
  {
    number_type na;
    if(numbers.get_number(a, na))
      return true; // not found, it's a root
    else
      return uuf.is_root(na);
  }

  bool is_root(typename numbering<T>::const_iterator it) const
  {
    return uuf.is_root(it-numbers.begin());
  }

  size_type number(const T &a)
  {
    size_type n=numbers.number(a);

    if(n>=uuf.size())
      uuf.resize(numbers.size());

    INVARIANT(uuf.size()==numbers.size(), "container sizes must match");

    return n;
  }

  void clear()
  {
    numbers.clear();
    uuf.clear();
  }

  void isolate(typename numbering<T>::const_iterator it)
  {
    uuf.isolate(it-numbers.begin());
  }

  void isolate(const T &a)
  {
    uuf.isolate(number(a));
  }

  bool get_number(const T &a, number_type &n) const
  {
    return numbers.get_number(a, n);
  }

  size_t size() const { return numbers.size(); }

  T &operator[](size_type t) { return numbers[t]; }
  const T &operator[](size_type t) const { return numbers[t]; }

  iterator begin() { return numbers.begin(); }
  const_iterator begin() const { return numbers.begin(); }
  const_iterator cbegin() const { return numbers.cbegin(); }

  iterator end() { return numbers.end(); }
  const_iterator end() const { return numbers.end(); }
  const_iterator cend() const { return numbers.cend(); }

protected:
  unsigned_union_find uuf;
  using subt = numbering<T>;
};

#endif // CPROVER_UTIL_UNION_FIND_H
