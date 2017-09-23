/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#ifndef CPROVER_GOTO_SYMEX_SLICE_H
#define CPROVER_GOTO_SYMEX_SLICE_H

#include "symex_target_equation.h"

// slice an equation with respect to the assertions contained therein
void slice(symex_target_equationt &equation);

// this simply slices away anything after the last assertion
void simple_slice(symex_target_equationt &equation);

// Slice the symex trace with respect to a list of given expressions
void slice(symex_target_equationt &equation,
           const expr_listt &expressions);

// Collects "open" variables that are used but not assigned

using symbol_sett = std::unordered_set<irep_idt, irep_id_hash>;

void collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables);

#endif // CPROVER_GOTO_SYMEX_SLICE_H
