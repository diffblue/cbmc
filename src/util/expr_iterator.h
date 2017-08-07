/*******************************************************************\

 Module: exprt iterator module

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_ITERATOR_H
#define CPROVER_UTIL_EXPR_ITERATOR_H

#include <iterator>
#include <functional>
#include <set>
#include <algorithm>
#include "expr.h"
#include "invariant.h"

// Forward declarations - table of contents

/// \file Forward depth-first search iterators
/// These iterators' copy operations are expensive, so use auto&, and avoid
/// std::next(), std::prev() and post-increment iterator
///
/// Non-const iterators dereference to const exprt (for use with STL
/// algorithms) but have an extra .mutate() method. That method is used
/// to access non-const exprt reference but is an expensive operation

/// Naive depth-first-search iterator with .mutate method for
/// modifying exprt under the iterator.
class depth_iteratort;
/// Naive depth-first-search iterator.
class const_depth_iteratort;
/// Depth first-search iterator with duplicate avoidance (skips over
/// duplicates, shows only first encountered child)
/// Slower iteration than naive version. Very expensive copy.
class const_unique_depth_iteratort;

/// Helper class for depth_iterator_baset
struct depth_iterator_expr_statet final
{
  typedef std::vector<exprt>::const_iterator operands_iteratort;
  inline depth_iterator_expr_statet(
    const exprt &expr,
    operands_iteratort it,
    operands_iteratort end):
    expr(expr), it(it), end(end) { }
  std::reference_wrapper<const exprt> expr;
  operands_iteratort it;
  operands_iteratort end;
};

inline bool operator==(
  const depth_iterator_expr_statet &left,
  const depth_iterator_expr_statet &right)
{ return left.it==right.it && left.expr.get()==right.expr.get(); }


/// Depth first search iterator base - iterates over supplied expression
/// and all its operands recursively.
/// Base class using CRTP
/// Do override .push_expr method of this class, but when doing so
/// make this class a friend so it has access to that overridden .push_expr
/// method in the child class
template<typename depth_iterator_t>
class depth_iterator_baset
{
public:
  typedef void difference_type;   // NOLINT Required by STL
  typedef exprt value_type;       // NOLINT
  typedef const exprt *pointer;   // NOLINT
  typedef const exprt &reference; // NOLINT
  typedef std::forward_iterator_tag iterator_category; // NOLINT
  bool operator==(const depth_iterator_t &other) const
  {
    return m_stack==other.m_stack;
  }

  /// Preincrement operator
  /// Do not call on the end() iterator
  depth_iterator_t &operator++()
  {
    PRECONDITION(!m_stack.empty());
    while(true)
    {
      if(m_stack.back().it==m_stack.back().end)
      {
        m_stack.pop_back();
        if(m_stack.empty())
          break;
      }
      // Check eg. if we haven't seen this node before
      else if(this->downcast().push_expr(*m_stack.back().it))
        break;
      m_stack.back().it++;
    }
    return this->downcast();
  }

  /// Post-increment operator
  /// Expensive copy. Avoid if possible
  depth_iterator_t operator++(int)
  {
    depth_iterator_t tmp(*this);
    this->operator++();
    return tmp;
  }

  /// Dereference operator
  /// Dereferencing end() iterator is undefined behaviour
  const exprt &operator*() const
  {
    PRECONDITION(!m_stack.empty());
    return m_stack.back().expr.get();
  }

  /// Dereference operator (member access)
  /// Dereferencing end() iterator is undefined behaviour
  const exprt *operator->() const
  { return &**this; }

protected:
  /// Create end iterator
  depth_iterator_baset()=default;

  /// Create begin iterator, starting at the supplied node
  explicit depth_iterator_baset(const exprt &root)
  { this->push_expr(root); }

  /// Destructor
  /// Protected to discourage upcasting
  ~depth_iterator_baset()=default;

  depth_iterator_baset(const depth_iterator_baset &)=default;
  depth_iterator_baset(depth_iterator_baset &&other)
  { m_stack=std::move(other.m_stack); }
  depth_iterator_baset &operator=(const depth_iterator_baset&)=default;
  depth_iterator_baset &operator=(depth_iterator_baset &&other)
  { m_stack=std::move(other.m_stack); }

  /// Obtain non-const exprt reference. Performs a copy-on-write on
  /// the root node as a side effect. To be called only if a the root
  /// is a non-const exprt. Do not call on the end() iterator
  exprt &mutate()
  {
    PRECONDITION(!m_stack.empty());
    auto expr=std::ref(const_cast<exprt &>(m_stack.front().expr.get()));
    for(auto &state : m_stack)
    {
      auto &operands=expr.get().operands();
      const auto i=operands.size()-(state.end-state.it);
      const auto it=operands.begin()+i;
      state.expr=expr.get();
      state.it=it;
      state.end=operands.end();
      if(!(state==m_stack.back()))
      {
        expr=std::ref(*it);
      }
    }
    return expr.get();
  }

  /// Pushes expression onto the stack
  /// If overridden, this function should be called from the inheriting
  /// class by the override function
  /// \return true if element was successfully pushed onto the stack,
  /// false otherwise
  /// If returning false, child will not be iterated over
  bool push_expr(const exprt &expr)
  {
    m_stack.emplace_back(expr, expr.operands().begin(), expr.operands().end());
    return true;
  }

private:
  std::vector<depth_iterator_expr_statet> m_stack;

  depth_iterator_t &downcast()
  { return static_cast<depth_iterator_t &>(*this); }
};

template<typename T, typename std::enable_if<
  std::is_base_of<depth_iterator_baset<T>, T>::value, int>::type=0>
bool operator!=(
  const T &left,
  const T &right)
{ return !(left==right); }

class const_depth_iteratort final:
  public depth_iterator_baset<const_depth_iteratort>
{
public:
  /// Create iterator starting at the supplied node (root)
  explicit const_depth_iteratort(const exprt &expr):
    depth_iterator_baset(expr) { }
  /// Create an end iterator
  const_depth_iteratort()=default;
};

class depth_iteratort final:
  public depth_iterator_baset<depth_iteratort>
{
public:
  /// Create an end iterator
  depth_iteratort()=default;
  /// Create iterator starting at the supplied node (root)
  /// All mutations of the child nodes will be reflected on this node
  explicit depth_iteratort(exprt &expr):
    depth_iterator_baset(expr) { }
  /// Obtain non-const reference to the pointed exprt instance
  /// Modifies root expression
  exprt &mutate()
  { return depth_iterator_baset::mutate(); }
};

class const_unique_depth_iteratort final:
  public depth_iterator_baset<const_unique_depth_iteratort>
{
  friend depth_iterator_baset;
public:
  /// Create iterator starting at the supplied node (root)
  explicit const_unique_depth_iteratort(const exprt &expr):
    depth_iterator_baset(expr),
    m_traversed({ expr }) { }
  /// Create an end iterator
  const_unique_depth_iteratort()=default;
private:
  /// Push expression onto the stack and add to the set of traversed exprts
  bool push_expr(const exprt &expr) // "override" - hide base class method
  {
    const bool inserted=this->m_traversed.insert(expr).second;
    if(inserted)
      depth_iterator_baset::push_expr(expr);
    return inserted;
  }
  std::set<exprt> m_traversed;
};

#endif
