/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory models for partial order concurrency

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_PSO_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_PSO_H

#include "memory_model_tso.h"

class memory_model_psot:public memory_model_tsot
{
public:
  memory_model_psot(const namespacet &_ns, guard_managert &guard_manager)
    : memory_model_tsot(_ns, guard_manager), guard_manager(guard_manager)
  {
  }

  virtual void operator()(symex_target_equationt &equation);

protected:
  virtual bool program_order_is_relaxed(
    partial_order_concurrencyt::event_it e1,
    partial_order_concurrencyt::event_it e2) const;

private:
  /// Used to initialize guards in SSA steps
  guard_managert &guard_manager;
};

#endif // CPROVER_GOTO_SYMEX_MEMORY_MODEL_PSO_H
