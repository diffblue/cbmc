/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// History for path-based symbolic simulator

#ifndef CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H
#define CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H

#include <cassert>
#include <limits>

#include <util/base_exceptions.h>
#include <util/std_expr.h>

#include "loc_ref.h"

class path_symex_stept;

// This is a reference to a path_symex_stept,
// and is really cheap to copy. These references are stable,
// even though the underlying vector is not.
class path_symex_step_reft
{
public:
  explicit path_symex_step_reft(
    class path_symex_historyt &_history):
    index(std::numeric_limits<std::size_t>::max()),
    history(&_history)
  {
  }

  path_symex_step_reft():
    index(std::numeric_limits<std::size_t>::max()), history(nullptr)
  {
  }

  bool is_nil() const
  {
    return index==std::numeric_limits<std::size_t>::max();
  }

  path_symex_historyt &get_history() const
  {
    INVARIANT_STRUCTURED(
      history!=nullptr, nullptr_exceptiont, "history is null");
    return *history;
  }

  // pre-decrement
  path_symex_step_reft &operator--();

  path_symex_stept &operator*() const { return get(); }
  path_symex_stept *operator->() const { return &get(); }

  void generate_successor();

  // build a forward-traversable version of the history
  void build_history(std::vector<path_symex_step_reft> &dest) const;

protected:
  // we use a vector to store all steps
  std::size_t index;
  class path_symex_historyt *history;

  path_symex_stept &get() const;
};

class decision_proceduret;

// the actual history node
class path_symex_stept
{
public:
  enum kindt
  {
    NON_BRANCH, BRANCH_TAKEN, BRANCH_NOT_TAKEN
  } branch;

  bool is_branch_taken() const
  {
    return branch==BRANCH_TAKEN;
  }

  bool is_branch_not_taken() const
  {
    return branch==BRANCH_NOT_TAKEN;
  }

  bool is_branch() const
  {
    return branch==BRANCH_TAKEN || branch==BRANCH_NOT_TAKEN;
  }

  path_symex_step_reft predecessor;

  // the thread that did the step
  unsigned thread_nr;

  // the instruction that was executed
  loc_reft pc;

  exprt guard, ssa_rhs;
  exprt full_lhs;
  symbol_exprt ssa_lhs;

  bool hidden;

  path_symex_stept():
    branch(NON_BRANCH),
    thread_nr(0),
    guard(nil_exprt()),
    ssa_rhs(nil_exprt()),
    full_lhs(nil_exprt()),
    hidden(false)
  {
  }

  // interface to solvers; this converts a single step
  void convert(decision_proceduret &dest) const;

  void output(std::ostream &) const;
};

// converts the full history
inline decision_proceduret &operator<<(
  decision_proceduret &dest,
  path_symex_step_reft src)
{
  while(!src.is_nil())
  {
    src->convert(dest);
    --src;
  }

  return dest;
}

// this stores the forest of histories
class path_symex_historyt
{
public:
  typedef std::vector<path_symex_stept> step_containert;
  step_containert step_container;

  // TODO: consider typedefing path_symex_historyt
  void clear()
  {
    step_container.clear();
  }
};

inline void path_symex_step_reft::generate_successor()
{
  INVARIANT_STRUCTURED(
    history!=nullptr, nullptr_exceptiont, "history is null");
  path_symex_step_reft old=*this;
  index=history->step_container.size();
  history->step_container.push_back(path_symex_stept());
  history->step_container.back().predecessor=old;
}

inline path_symex_step_reft &path_symex_step_reft::operator--()
{
  *this=get().predecessor;
  return *this;
}

inline path_symex_stept &path_symex_step_reft::get() const
{
  INVARIANT_STRUCTURED(
    history!=nullptr, nullptr_exceptiont, "history is null");
  assert(!is_nil());
  return history->step_container[index];
}

#endif // CPROVER_PATH_SYMEX_PATH_SYMEX_HISTORY_H
