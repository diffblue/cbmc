/*******************************************************************\

Module: Compute natural loops in a goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Compute natural loops in a goto_function.
///
/// A natural loop is when the nodes and edges of a graph make one self-encapsulating
/// circle with no incoming edges from external nodes. For example A -> B -> C -> D -> A
/// is a natural loop, but if B has an incoming edge from X, then it isn't a natural loop,
/// because X is an external node. Outgoing edges don't affect the natural-ness of a loop.
///
/// /ref cfg_dominators_templatet provides the dominator analysis used to determine if a nodes
/// children can only be reached through itself and is thus part of a natural loop.

#ifndef CPROVER_ANALYSES_NATURAL_LOOPS_H
#define CPROVER_ANALYSES_NATURAL_LOOPS_H

#include <stack>
#include <iosfwd>
#include <set>

#include <goto-programs/goto_model.h>
#include <util/const_cast_iterator.h>

#include "cfg_dominators.h"

/// Main driver for working out if a class (normally goto_programt) has any natural loops.
/// \ref compute takes an entire goto_programt, iterates over the instructions and for
/// any backwards jumps attempts to find out if it's a natural loop.
///
/// All instructions in a natural loop are stored into \ref loop_map, keyed by
/// their head - the target of the backwards goto jump.
///
/// \tparam P the program representation and needs:
///     [field] instruction which is an iterable of type T.
/// \tparam T iterator of the particular node type, ex: std::list<...>::iterator.
///     The object this iterator holds needs:
///         [function] is_backwards_goto() returning a bool.
///         [function] get_target() which returns an object that needs:
///             [field] location_number which returns an unsigned int.
class natural_loops_baset
{
public:
  void operator()(const goto_programt &program)
  {
    compute(program);
  }

  const cfg_dominatorst &get_dominator_info() const
  {
    return cfg_dominators;
  }

protected:
  cfg_dominatorst cfg_dominators;
  typedef cfg_dominatorst::cfgt::nodet nodet;

  typedef goto_programt::const_targett targett;

  std::map<targett, std::set<targett>> compute(const goto_programt &program);
  std::set<targett> compute_natural_loop(targett, targett);
};

template<typename Container, typename ConstIterator>
typename Container::const_iterator get_iterator(
  const Container &, const ConstIterator ci)
{
  return ci;
}

template<typename Container, typename ConstIterator>
typename Container::iterator get_iterator(
  Container &container, const ConstIterator ci)
{
  return get_nonconst_iterator(container, ci);
}

template<class P, class T>
class natural_loops_templatet : public natural_loops_baset
{
public:
  typedef std::set<T> natural_loopt;

  // map loop headers to loops
  typedef std::map<T, natural_loopt> loop_mapt;

  loop_mapt loop_map;

  natural_loops_templatet() = default;
  void operator()(P &program)
  {
    for(const auto &found_loop : compute(program))
    {
      auto &loop =
        loop_map[get_iterator(program.instructions, found_loop.first)];
      for(auto instruction_iter : found_loop.second)
        loop.insert(get_iterator(program.instructions, instruction_iter));
    }
  }

  natural_loops_templatet(P &program)
  {
    (*this)(program);
  }

  void output(std::ostream &stream) const;
};

/// Print all natural loops that were found
template<class P, class T>
void natural_loops_templatet<P, T>::output(std::ostream &out) const
{
  for(const auto &loop : loop_map)
  {
    unsigned n=loop.first->location_number;

    out << n << " is head of { ";
    for(typename natural_loopt::const_iterator l_it=loop.second.begin();
        l_it!=loop.second.end(); ++l_it)
    {
      if(l_it!=loop.second.begin())
        out << ", ";
      out << (*l_it)->location_number;
    }
    out << " }\n";
  }
}

typedef
  natural_loops_templatet<const goto_programt, goto_programt::const_targett>
  natural_loopst;

typedef natural_loops_templatet<goto_programt, goto_programt::targett>
    natural_loops_mutablet;

void show_natural_loops(
  const goto_modelt &,
  std::ostream &out);

#endif // CPROVER_ANALYSES_NATURAL_LOOPS_H
