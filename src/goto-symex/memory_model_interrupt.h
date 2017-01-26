/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Lihao Liang, lihao.liang@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_MEMORY_MODEL_INTERRUPT_H
#define CPROVER_GOTO_SYMEX_MEMORY_MODEL_INTERRUPT_H

#include "memory_model_sc.h"

class memory_model_interruptt:public memory_model_sct
{
public:
  explicit memory_model_interruptt(const namespacet &_ns):
    memory_model_sct(_ns)
  {
  }

  virtual void operator()(symex_target_equationt &equation);
  
protected:
  void read_from(symex_target_equationt &equation);
  void from_read(symex_target_equationt &equation);
  void write_serialization_external(symex_target_equationt &equation);

private:
  per_thread_mapt per_thread_map;
  exprt last(const event_it &from, const event_it &to);
};

#endif
