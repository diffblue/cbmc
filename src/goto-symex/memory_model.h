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
  virtual void operator()(symex_target_equationt &)=0;
  virtual ~memory_model_baset();

  typedef symex_target_equationt::SSA_stept eventt;
  typedef symex_target_equationt::SSA_stepst eventst;
  
protected:
  typedef std::vector<const eventt *> event_listt;
  event_listt reads, writes;
  
  void build_event_lists(symex_target_equationt &);
};

class memory_model_sct:public memory_model_baset
{
public:
  virtual void operator()(symex_target_equationt &equation);
  
protected:
  virtual void read_from(symex_target_equationt &equation);  
};

#endif

