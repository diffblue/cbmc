/*******************************************************************\

Module: Constant Function Pointer Propagation

Author: Vincent Nimal

\*******************************************************************/

/// \file
/// Constant Function Pointer Propagation

#ifndef CPROVER_MUSKETEER_PROPAGATE_CONST_FUNCTION_POINTERS_H
#define CPROVER_MUSKETEER_PROPAGATE_CONST_FUNCTION_POINTERS_H

class goto_modelt;
class message_handlert;

/* Note that it only propagates from MAIN, following the CFG, without
   resolving non-constant function pointers. This is of particular interest
   when used in conjunction with goto_partial_inline, so that it explores
   inlined functions accepting generic functions (pthread_create in
   particular) in their context, preventing a huge overapproximation of a
   functions-based exploration in remove_function_pointers. */

void propagate_const_function_pointers(
  goto_modelt &,
  message_handlert &);

#endif // CPROVER_MUSKETEER_PROPAGATE_CONST_FUNCTION_POINTERS_H
