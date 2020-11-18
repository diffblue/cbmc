/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory models for partial order concurrency

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_SC_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_SC_H

#include "memory_model.h"

class memory_model_sct:public memory_model_baset
{
public:
  explicit memory_model_sct(const namespacet &_ns):
    memory_model_baset(_ns)
  {
  }

  virtual void operator()(symex_target_equationt &equation, message_handlert &);

protected:
  virtual exprt before(event_it e1, event_it e2);
  virtual bool program_order_is_relaxed(
    partial_order_concurrencyt::event_it e1,
    partial_order_concurrencyt::event_it e2) const;

  void build_per_thread_map(
    const symex_target_equationt &equation,
    per_thread_mapt &dest) const;
  void thread_spawn(
    symex_target_equationt &equation,
    const per_thread_mapt &per_thread_map);
  void program_order(symex_target_equationt &equation);
  void from_read(symex_target_equationt &equation);
  void write_serialization_external(symex_target_equationt &equation);
};

#endif // CPROVER_GOTO_SYMEX_MEMORY_MODEL_SC_H
