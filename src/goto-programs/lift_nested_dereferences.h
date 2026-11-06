/*******************************************************************\

Module: Lift nested dereferences into temporaries

Author: Kiro

\*******************************************************************/

/// \file
/// Lift nested (chained) dereferences into temporaries.
///
/// A chained dereference such as `a->b->c` dereferences the pointer `a->b`,
/// which is itself the result of a dereference. This transformation rewrites
/// such expressions into the equivalent
///
///     tmp = a->b;
///     ... tmp->c ...
///
/// by introducing a fresh local temporary for the result of the inner
/// dereference and assigning it on a preceding instruction. The rewrite is
/// applied innermost-first, so arbitrarily deep chains are flattened.
///
/// This is semantics-preserving. It has two benefits:
/// * the same pointer is not dereferenced more than once (chained
///   dereferences are otherwise re-evaluated for each access), and
/// * the intermediate pointer becomes an ordinary local variable with its own
///   object identity, which makes downstream analyses (e.g. the value-set
///   dereference and auto-object initialisation in goto-symex) treat it the
///   same way they treat a hand-written intermediate variable.
///
/// The model-level entry point conservatively does nothing for concurrent
/// programs: reusing a single read of a possibly-shared intermediate pointer
/// would remove thread interleavings and could hide data-race-dependent bugs.

#ifndef CPROVER_GOTO_PROGRAMS_LIFT_NESTED_DEREFERENCES_H
#define CPROVER_GOTO_PROGRAMS_LIFT_NESTED_DEREFERENCES_H

#include <util/irep.h>

class goto_functiont;
class goto_modelt;
class symbol_table_baset;

/// Lift nested dereferences in a single function.
/// \param goto_function: the function to transform
/// \param symbol_table: symbol table to add temporaries to
/// \param mode: language mode for the temporaries (e.g. ID_C)
void lift_nested_dereferences(
  goto_functiont &goto_function,
  symbol_table_baset &symbol_table,
  const irep_idt &mode);

/// Lift nested dereferences in all functions of \p goto_model.
void lift_nested_dereferences(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_LIFT_NESTED_DEREFERENCES_H
