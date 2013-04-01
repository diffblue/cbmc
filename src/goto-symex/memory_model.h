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
  memory_model_baset();
  virtual ~memory_model_baset();

  virtual void operator()(symex_target_equationt &)=0;
  
  typedef symex_target_equationt::SSA_stept eventt;
  typedef symex_target_equationt::SSA_stepst eventst;
  
protected:
  typedef std::vector<const eventt *> event_listt;
  
  // global
  event_listt reads, writes;

  // a per-thread numbering of the events
  typedef std::map<const eventt *, unsigned> numberingt;
  numberingt numbering;
  
  void build_event_lists(symex_target_equationt &);
  
  // program order
  bool po(const eventt &e1, const eventt &e2)
  {
    return e1.source.thread_nr==e2.source.thread_nr &&
           numbering[&e1]<numbering[&e2];
  }

  // produce fresh symbols  
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(const std::string &prefix);
};

class memory_model_sct:public memory_model_baset
{
public:
  virtual void operator()(symex_target_equationt &equation);
  
protected:
  virtual void read_from(symex_target_equationt &equation);  
};

#endif

