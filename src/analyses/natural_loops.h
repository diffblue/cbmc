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

template <class, class>
class natural_loops_templatet;

/// A natural loop, specified as a set of instructions
template <class P, class T>
class natural_loop_templatet
{
  typedef natural_loops_templatet<P, T> natural_loopst;
  // For natural_loopst to directly manipulate loop_instructions, cf. clients
  // which should use the public iterface:
  friend natural_loopst;

  typedef std::set<T> loop_instructionst;
  loop_instructionst loop_instructions;

public:
  explicit natural_loop_templatet(natural_loopst &natural_loops)
    : natural_loops(natural_loops)
  {
  }

  /// Returns true if \p instruction is in this loop
  bool contains(const T instruction) const
  {
    return natural_loops.loop_contains(*this, instruction);
  }

  /// Get the \ref natural_loopst analysis this loop relates to
  const natural_loopst &get_natural_loops() const
  {
    return natural_loops;
  }
  /// Get the \ref natural_loopst analysis this loop relates to
  natural_loopst &get_natural_loops()
  {
    return natural_loops;
  }

  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename loop_instructionst::const_iterator const_iterator;

  /// Iterator over this loop's instructions
  const_iterator begin() const
  {
    return loop_instructions.begin();
  }

  /// Iterator over this loop's instructions
  const_iterator end() const
  {
    return loop_instructions.end();
  }

  /// Number of instructions in this loop
  std::size_t size() const
  {
    return loop_instructions.size();
  }

  /// Returns true if this loop contains no instructions
  bool empty() const
  {
    return loop_instructions.empty();
  }

  /// Adds \p instruction to this loop. The caller must verify that the added
  /// instruction does not alter loop structure; if it does they must discard
  /// and recompute the related \ref natural_loopst instance.
  void insert_instruction(const T instruction)
  {
    loop_instructions.insert(instruction);
  }

private:
  natural_loopst &natural_loops;
};

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
template<class P, class T>
class natural_loops_templatet
{
public:
  typedef natural_loop_templatet<P, T> natural_loopt;
  // map loop headers to loops
  typedef std::map<T, natural_loopt> loop_mapt;

  loop_mapt loop_map;

  void operator()(P &program)
  {
    compute(program);
  }

  void output(std::ostream &) const;

  const cfg_dominators_templatet<P, T, false> &get_dominator_info() const
  {
    return cfg_dominators;
  }

  /// Returns true if \p instruction is in \p loop
  bool loop_contains(const natural_loopt &loop, const T instruction) const
  {
    return loop.loop_instructions.count(instruction);
  }

  /// Returns true if \p instruction is the header of any loop
  bool is_loop_header(const T instruction) const
  {
    return loop_map.count(instruction);
  }

  natural_loops_templatet()
  {
  }

  explicit natural_loops_templatet(P &program)
  {
    compute(program);
  }

  // The loop structures stored in `loop_map` contain back-pointers to this
  // class, so we forbid copying or moving the analysis struct. If this becomes
  // necessary then either add a layer of indirection or update the loop_map
  // back-pointers on copy/move.
  natural_loops_templatet(const natural_loops_templatet &) = delete;
  natural_loops_templatet(natural_loops_templatet &&) = delete;
  natural_loops_templatet &operator=(const natural_loops_templatet &) = delete;
  natural_loops_templatet &operator=(natural_loops_templatet &&) = delete;

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

void show_natural_loops(
  const goto_modelt &,
  std::ostream &out);

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

  auto insert_result = loop_map.emplace(n, natural_loopt{*this});
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
      std::pair<typename natural_loopt::const_iterator, bool> result =
        loop.loop_instructions.insert(q);
      if(result.second)
        stack.push(q);
    }
  }
}

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

#endif // CPROVER_ANALYSES_NATURAL_LOOPS_H
