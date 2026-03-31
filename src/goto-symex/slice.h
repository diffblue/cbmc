/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#ifndef CPROVER_GOTO_SYMEX_SLICE_H
#define CPROVER_GOTO_SYMEX_SLICE_H

#include <util/irep.h>

#include <list>
#include <unordered_set>
#include <vector>

class exprt;
class symex_target_equationt;
class SSA_stept; // IWYU pragma: keep

// slice an equation with respect to the assertions contained therein
void slice(symex_target_equationt &equation);

/// Undo whatever has been done by `slice`
void revert_slice(symex_target_equationt &);

// this simply slices away anything after the last assertion
void simple_slice(symex_target_equationt &equation);

// Slice the symex trace with respect to a list of given expressions
void slice(
  symex_target_equationt &equation,
  const std::list<exprt> &expressions);

// Collects "open" variables that are used but not assigned

typedef std::unordered_set<irep_idt> symbol_sett;

void collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables);

/// Compute the cone of influence for a single assertion.
/// Walks backwards from \p assertion_step through \p steps, collecting
/// all steps that the assertion depends on (assignments defining symbols
/// used in the assertion condition/guard, assumptions, and constraints).
/// \param steps: the SSA steps to search (up to \p num_steps entries)
/// \param assertion_step: iterator pointing to the assertion
/// \param num_steps: number of steps to consider from the beginning
/// \return pointers to the steps in the cone (including the assertion)
std::vector<const SSA_stept *> cone_of_influence(
  const std::list<SSA_stept> &steps,
  std::list<SSA_stept>::const_iterator assertion_step,
  std::size_t num_steps);

#endif // CPROVER_GOTO_SYMEX_SLICE_H
