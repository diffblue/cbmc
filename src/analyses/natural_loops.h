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

#include "cfg_dominators.h"
#include "loop_analysis.h"

/// Main driver for working out if a class (normally goto_programt) has any natural loops.
/// \ref compute takes an entire goto_programt, iterates over the instructions and for
/// any backwards jumps attempts to find out if it's a natural loop.
///
/// All instructions in a natural loop are stored into \ref loop_map, keyed by
/// their head - the target of the backwards goto jump.
///
/// \tparam P: the program representation and needs:
///   * [field] instruction which is an iterable of type T.
/// \tparam T: iterator of the particular node type, e.g.
///   std::list<...>::iterator. The object this iterator holds needs:
///   * [function] is_backwards_goto() returning a bool.
///   * [function] get_target() which returns an object that needs:
///     * [field] location_number which is an unsigned int.
template <class P, class T>
class natural_loops_templatet : public loop_analysist<T>
{
  typedef loop_analysist<T> parentt;

public:
  typedef typename parentt::loopt natural_loopt;

  void operator()(P &program)
  {
    compute(program);
  }

  const cfg_dominators_templatet<P, T, false> &get_dominator_info() const
  {
    return cfg_dominators;
  }

  natural_loops_templatet()
  {
  }

  explicit natural_loops_templatet(P &program)
  {
    compute(program);
  }

protected:
  cfg_dominators_templatet<P, T, false> cfg_dominators;
  typedef typename cfg_dominators_templatet<P, T, false>::cfgt::nodet nodet;

  void compute(P &program);
  void compute_natural_loop(T, T);
};

/// A concretized version of
/// \ref natural_loops_templatet<const goto_programt, goto_programt::const_targett>
class natural_loopst:
    public natural_loops_templatet<const goto_programt,
                                   goto_programt::const_targett>
{
};

typedef natural_loops_templatet<goto_programt, goto_programt::targett>
    natural_loops_mutablet;

inline void show_natural_loops(const goto_modelt &goto_model, std::ostream &out)
{
  show_loops<natural_loopst>(goto_model, out);
}

#ifdef DEBUG
#include <iostream>
#endif

/// Finds all back-edges and computes the natural loops
template<class P, class T>
void natural_loops_templatet<P, T>::compute(P &program)
{
  cfg_dominators(program);

#ifdef DEBUG
  cfg_dominators.output(std::cout);
#endif

  // find back-edges m->n
  for(T m_it=program.instructions.begin();
      m_it!=program.instructions.end();
      ++m_it)
  {
    if(m_it->is_backwards_goto())
    {
      const auto &target=m_it->get_target();

      if(target->location_number<=m_it->location_number)
      {
        #ifdef DEBUG
        std::cout << "Computing loop for "
                  << m_it->location_number << " -> "
                  << target->location_number << "\n";
        #endif

        if(cfg_dominators.dominates(target, m_it))
          compute_natural_loop(m_it, target);
      }
    }
  }
}

/// Computes the natural loop for a given back-edge (see Muchnick section 7.4)
template<class P, class T>
void natural_loops_templatet<P, T>::compute_natural_loop(T m, T n)
{
  assert(n->location_number<=m->location_number);

  std::stack<T> stack;

  auto insert_result = parentt::loop_map.emplace(n, natural_loopt{});
  // Note the emplace *may* access a loop that already exists: this happens when
  // a given header has more than one incoming edge, such as
  // head: if(x) goto head; else goto head;
  // In this case this compute routine is run twice, one for each backedge, with
  // each adding whatever instructions can reach this 'm' (the program point
  // that branches to the loop header, 'n').
  natural_loopt &loop = insert_result.first->second;

  loop.insert_instruction(n);
  loop.insert_instruction(m);

  if(n!=m)
    stack.push(m);

  while(!stack.empty())
  {
    T p=stack.top();
    stack.pop();

    const nodet &node = cfg_dominators.get_node(p);

    for(const auto &edge : node.in)
    {
      T q=cfg_dominators.cfg[edge.first].PC;
      if(loop.insert_instruction(q))
        stack.push(q);
    }
  }
}

#endif // CPROVER_ANALYSES_NATURAL_LOOPS_H
