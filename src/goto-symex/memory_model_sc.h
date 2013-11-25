/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_SC_H
#define CPROVER_MEMORY_MODEL_SC_H

#include "memory_model.h"

class memory_model_sct:public memory_model_baset
{
public:
  inline explicit memory_model_sct(const namespacet &_ns):
    memory_model_baset(_ns)
  {
  }

  virtual void operator()(symex_target_equationt &equation);
  
protected:
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

#endif

