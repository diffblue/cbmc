/*******************************************************************\

Module: Constant Function Pointer Propagation

Author: Vincent Nimal

\*******************************************************************/

#ifndef PROPAGATE_CONST_FUNCTION_POINTERS_H
#define PROPAGATE_CONST_FUNCTION_POINTERS_H

class symbol_tablet;
class goto_functionst;
class message_handlert;

/* Note that it only propagates from MAIN, following the CFG, without
   resolving non-constant function pointers. This is of particular interest
   when used in conjunction with goto_partial_inline, so that it explores 
   inlined functions accepting generic functions (pthread_create in 
   particular) in their context, preventing a huge overapproximation of a 
   functions-based exploration in remove_function_pointers. */

void propagate_const_function_pointers(
  symbol_tablet& symbol_tables, 
  goto_functionst& goto_functions,
  message_handlert& message_handler);

#endif
