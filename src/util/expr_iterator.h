/*******************************************************************\

Module: exprt iterator module

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_ITERATOR_H
#define CPROVER_UTIL_EXPR_ITERATOR_H

#include <deque>
#include <iterator>
#include <functional>
#include <set>
#include <algorithm>
#include "expr.h"
#include "invariant.h"

// Forward declarations - table of contents

/// \file
/// Forward depth-first search iterators
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
  typedef exprt::operandst::const_iterator operands_iteratort;
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
{
  return distance(left.it, left.end) == distance(right.it, right.end) &&
         left.expr.get() == right.expr.get();
}

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

  template <typename other_depth_iterator_t>
  friend class depth_iterator_baset;

  template <typename other_depth_iterator_t>
  bool operator==(
    const depth_iterator_baset<other_depth_iterator_t> &other) const
  {
    return m_stack==other.m_stack;
  }

  template <typename other_depth_iterator_t>
  bool operator!=(
    const depth_iterator_baset<other_depth_iterator_t> &other) const
  {
    return !(*this == other);
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

  depth_iterator_t &next_sibling_or_parent()
  {
    PRECONDITION(!m_stack.empty());
    m_stack.pop_back();
    if(!m_stack.empty())
    {
      ++m_stack.back().it;
      return ++(*this);
    }
    return this->downcast();
  }

  /// Post-increment operator
  /// Expensive copy. Avoid if possible
  depth_iterator_t operator++(int)
  {
    depth_iterator_t tmp(this->downcast());
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

  const exprt &get_root()
  {
    return m_stack.front().expr.get();
  }

  /// Obtain non-const exprt reference. Performs a copy-on-write on the root
  /// node as a side effect.
  /// \remarks
  ///   To be called only if a the root is a non-const exprt.
  ///   Do not call on the end() iterator
  exprt &mutate()
  {
    PRECONDITION(!m_stack.empty());
    // Cast the root expr to non-const
    exprt *expr = &const_cast<exprt &>(get_root());
    for(auto &state : m_stack)
    {
      // This deliberately breaks sharing as expr is now non-const
      auto &operands = expr->operands();
      // Get iterators into the operands of the new expr corresponding to the
      // ones into the operands of the old expr
      const auto i=operands.size()-(state.end-state.it);
      const auto it=operands.begin()+i;
      state.expr = *expr;
      state.it=it;
      state.end=operands.end();
      // Get the expr for the next level down to use in the next iteration
      if(!(state==m_stack.back()))
      {
        expr = &*it;
      }
    }
    return *expr;
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
  std::deque<depth_iterator_expr_statet> m_stack;

  depth_iterator_t &downcast()
  { return static_cast<depth_iterator_t &>(*this); }
};

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
private:
  /// If this is non-empty then the root is currently const and this function
  /// must be called before any mutations occur
  std::function<exprt &()> mutate_root;

public:
  /// Create an end iterator
  depth_iteratort()=default;

  /// Create iterator starting at the supplied node (root)
  /// All mutations of the child nodes will be reflected on this node
  /// \param expr: The root node to begin iteration at
  explicit depth_iteratort(exprt &expr) : depth_iterator_baset(expr)
  {
  }

  /// Create iterator starting at the supplied node (root)
  /// If mutations of the child nodes are required then the passed
  /// mutate_root function will be called to get a non-const copy of the same
  /// root on which the mutations will be done.
  /// \param expr: The root node to begin iteration at
  /// \param mutate_root: The function to call to get a non-const copy of the
  ///   same root expression passed in the expr parameter
  explicit depth_iteratort(
    const exprt &expr,
    std::function<exprt &()> mutate_root)
    : depth_iterator_baset(expr), mutate_root(std::move(mutate_root))
  {
    // If you don't provide a mutate_root function then you must pass a
    // non-const exprt (use the other constructor).
    PRECONDITION(this->mutate_root);
  }

  /// Obtain non-const reference to the exprt instance currently pointed to
  /// by the iterator.
  /// If the iterator is currently using a const root exprt then calls
  /// mutate_root to get a non-const root and copies it if it is shared
  /// \returns A non-const reference to the element this iterator is
  ///   currently pointing to
  exprt &mutate()
  {
    if(mutate_root)
    {
      exprt &new_root = mutate_root();
      INVARIANT(
        &new_root.read() == &get_root().read(),
        "mutate_root must return the same root node that depth_iteratort was "
        "constructed with");
      mutate_root = nullptr;
    }
    return depth_iterator_baset::mutate();
  }
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
