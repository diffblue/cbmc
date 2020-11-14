/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory models for partial order concurrency

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_TSO_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_TSO_H

#include "memory_model_sc.h"

class memory_model_tsot:public memory_model_sct
{
public:
  explicit memory_model_tsot(const namespacet &_ns):
    memory_model_sct(_ns)
  {
  }

  virtual void operator()(symex_target_equationt &equation, message_handlert &);

protected:
  virtual exprt before(event_it e1, event_it e2);
  virtual bool program_order_is_relaxed(
    partial_order_concurrencyt::event_it e1,
    partial_order_concurrencyt::event_it e2) const;
  void program_order(symex_target_equationt &equation);
};

#endif // CPROVER_GOTO_SYMEX_MEMORY_MODEL_TSO_H
