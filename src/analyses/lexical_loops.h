/*******************************************************************\

Module: Compute lexical loops in a goto_function

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Compute lexical loops in a goto_function.
///
/// A lexical loop is a block of GOTO program instructions with a single entry
/// edge at the top and a single backedge leading from bottom to top, where
/// "top" and "bottom" refer to program order. The loop may have holes:
/// instructions which sit in between the top and bottom in program order, but
/// which can't reach the loop backedge. Lexical loops are a subset of the
/// natural loops, which are cheaper to compute and include most natural loops
/// generated from typical C code.
///
/// Example of a lexical loop:
///
///     1: x = x + 1
///        IF x < 5 GOTO 2
///        done = true (*)
///        GOTO 3 (*)
///     2: i = i + 1
///        IF i < 10 GOTO 1
///     3: RETURN x
///
/// Assuming there are no GOTOs outside the loop targeting label 2, this is a
/// lexical loop because the header (1) is the only entry point and the only
/// back-edge is the final conditional GOTO.
/// The instructions marked with a (*) are *not* in the loop; they are on a path
/// that always leaves the loop (once the IF x < 5 test is failed we are
/// certainly leaving the loop).

#ifndef CPROVER_ANALYSES_LEXICAL_LOOPS_H
#define CPROVER_ANALYSES_LEXICAL_LOOPS_H

#include <iosfwd>
#include <set>
#include <stack>

#include <goto-programs/goto_model.h>

#include "loop_analysis.h"

/// Main driver for working out if a class (normally goto_programt) has any
/// lexical loops. \ref compute takes an entire goto_programt, iterates over the
/// instructions and for any backwards jumps attempts to find out if it's a
/// lexical loop.
///
/// All instructions in a lexical loop are stored into \ref loop_map, keyed by
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
class lexical_loops_templatet : public loop_analysist<T>
{
  typedef loop_analysist<T> parentt;

public:
  typedef typename parentt::loopt lexical_loopt;

  void operator()(P &program)
  {
    compute(program);
  }

  lexical_loops_templatet() = default;

  explicit lexical_loops_templatet(P &program)
  {
    compute(program);
  }

  bool all_cycles_in_lexical_loop_form() const
  {
    return all_in_lexical_loop_form;
  }

  void output(std::ostream &out) const
  {
    parentt::output(out);
    if(!all_in_lexical_loop_form)
      out << "Note not all loops were in lexical loop form\n";
  }

  virtual ~lexical_loops_templatet() = default;

protected:
  void compute(P &program);
  bool compute_lexical_loop(T, T);

  bool all_in_lexical_loop_form = false;
};

typedef lexical_loops_templatet<
  const goto_programt,
  goto_programt::const_targett>
  lexical_loopst;

#ifdef DEBUG
#  include <iostream>
#endif

/// Finds all back-edges and computes the lexical loops
template <class P, class T>
void lexical_loops_templatet<P, T>::compute(P &program)
{
  all_in_lexical_loop_form = true;

  // find back-edges m->n
  for(auto it = program.instructions.begin(); it != program.instructions.end();
      ++it)
  {
    if(it->is_backwards_goto())
    {
      const auto &target = it->get_target();

      if(target->location_number <= it->location_number)
      {
#ifdef DEBUG
        std::cout << "Computing loop for " << it->location_number << " -> "
                  << target->location_number << "\n";
#endif

        if(!compute_lexical_loop(it, target))
          all_in_lexical_loop_form = false;
      }
    }
  }
}

/// Computes the lexical loop for a given back-edge by walking backwards from
/// the tail, abandoning the candidate loop if we stray outside the bounds of
/// the lexical region bounded by the head and tail, otherwise recording all
/// instructions that can reach the backedge as falling within the loop.
template <class P, class T>
bool lexical_loops_templatet<P, T>::compute_lexical_loop(
  T loop_tail,
  T loop_head)
{
  INVARIANT(
    loop_head->location_number <= loop_tail->location_number,
    "loop header should come lexically before the tail");

  std::stack<T> stack;
  std::set<T> loop_instructions;

  loop_instructions.insert(loop_head);
  loop_instructions.insert(loop_tail);

  if(loop_head != loop_tail)
    stack.push(loop_tail);

  while(!stack.empty())
  {
    T loop_instruction = stack.top();
    stack.pop();

    for(auto predecessor : loop_instruction->incoming_edges)
    {
      if(
        predecessor->location_number > loop_tail->location_number ||
        predecessor->location_number < loop_head->location_number)
      {
        // Not a lexical loop: has an incoming edge from outside.
        return false;
      }
      if(loop_instructions.insert(predecessor).second)
        stack.push(predecessor);
    }
  }

  auto insert_result = parentt::loop_map.emplace(
    loop_head, lexical_loopt{std::move(loop_instructions)});

  // If this isn't a new loop head (i.e. return_result.second is false) then we
  // have multiple backedges targeting one loop header: this is not in simple
  // lexical loop form.
  return insert_result.second;
}

inline void show_lexical_loops(const goto_modelt &goto_model, std::ostream &out)
{
  show_loops<lexical_loopst>(goto_model, out);
}

#endif // CPROVER_ANALYSES_LEXICAL_LOOPS_H
