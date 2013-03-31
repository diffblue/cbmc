/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_H
#define CPROVER_MEMORY_MODEL_H

#include <message.h>

#include "symex_target_equation.h"

class memory_model_baset:public messaget
{
public:
  virtual void operator()(symex_target_equationt &)
  {
  }
  
  virtual ~memory_model_baset();

protected:
};

class memory_model_sct:public memory_model_baset
{
protected:
  virtual void read_from();  
};

#endif

