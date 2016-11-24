/*******************************************************************\

Module: Fence insertion following criteria of Pensieve (PPoPP'05)

Author: Vincent Nimal

\*******************************************************************/

#ifndef CPROVER_PENSIEVE_H
#define CPROVER_PENSIEVE_H

#include <goto-instrument/wmm/wmm.h>
#include <goto-instrument/wmm/weak_memory.h>

class value_setst;
class goto_functionst;
class symbol_tablet;
class message_handlert;

void fence_pensieve(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  unsigned unwinding_bound,
  unsigned max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool naive_mode,
  message_handlert& message_handler);

#endif
