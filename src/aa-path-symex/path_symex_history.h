/*******************************************************************\

Module: History for path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_HISTORY_H
#define CPROVER_PATH_SYMEX_HISTORY_H

#include <cassert>
#include <limits>

#include <util/std_expr.h>

#include "loc_ref.h"

class path_symex_stept;

// This is a reference to a path_symex_stept,
// and is really cheap to copy. These references are stable,
// even though the underlying vector is not.
class path_symex_step_reft
{
public:
  explicit inline path_symex_step_reft(
    class path_symex_historyt &_history):
    index(std::numeric_limits<std::size_t>::max()),
    history(&_history)
  {
  }

  inline path_symex_step_reft():
    index(std::numeric_limits<std::size_t>::max()), history(0)
  {
  }
  
  inline bool is_nil() const
  {
    return index==std::numeric_limits<std::size_t>::max();
  }
  
  inline path_symex_historyt &get_history() const
  {
    assert(history!=0);
    return *history;
  }
  
  // pre-decrement
  inline path_symex_step_reft &operator--();
  
  inline path_symex_stept &operator*() const { return get(); }
  inline path_symex_stept *operator->() const { return &get(); }
  
  void generate_successor();

  // build a forward-traversible version of the history  
  void build_history(std::vector<path_symex_step_reft> &dest) const;

protected:
  // we use a vector to store all steps
  std::size_t index;
  class path_symex_historyt *history;
  
  inline path_symex_stept &get() const;
};

class decision_proceduret;

// the actual history node
class path_symex_stept
{
public:
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
static inline decision_proceduret &operator << (
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
  inline void clear()
  {
    step_container.clear();
  }
};

inline void path_symex_step_reft::generate_successor()
{
  assert(history!=0);
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
  assert(history!=0);
  assert(!is_nil());
  return history->step_container[index];
}

inline void path_symex_step_reft::build_history(
  std::vector<path_symex_step_reft> &dest) const
{
  path_symex_step_reft s=*this;
  while(!s.is_nil())
  {
    dest.push_back(s);
    --s;
  }
}

#endif
