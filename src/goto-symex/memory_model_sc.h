/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_SC_H
#define CPROVER_MEMORY_MODEL_SC_H

#include "memory_model.h"

#if 0
class memory_model_sct:public memory_model_baset
{
public:
  virtual void operator()(symex_target_equationt &equation);
  
protected:
  virtual void read_from(symex_target_equationt &equation);
  virtual void program_order(symex_target_equationt &equation);
  virtual void write_serialization_internal(symex_target_equationt &equation);
  virtual void write_serialization_external(symex_target_equationt &equation);
};
#endif

#endif

