/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_H
#define CPROVER_MEMORY_MODEL_H

#include "partial_order_concurrency.h"

class memory_model_baset:public partial_order_concurrencyt
{
public:
  memory_model_baset();
  virtual ~memory_model_baset();

  virtual void operator()(symex_target_equationt &)=0;
  
protected:
  typedef std::vector<const eventt *> event_listt;
  
  // global lists
  event_listt reads, writes;
  void build_event_lists(symex_target_equationt &);
  
  // a per-thread numbering of the events
  typedef std::map<irep_idt, unsigned> numberingt;
  numberingt numbering;
  
  // program order
  bool po(const eventt &e1, const eventt &e2)
  {
    return e1.source.thread_nr==e2.source.thread_nr &&
           numbering[id(e1)]<numbering[id(e2)];
  }

  // produce fresh symbols  
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(const std::string &prefix);
  
  // This gives us the choice symbol for a R-W pair;
  // built by the method below.
  typedef std::map<
    std::pair<irep_idt, irep_idt>, symbol_exprt> choice_symbolst;
  choice_symbolst choice_symbols;

  void read_from(symex_target_equationt &equation);
};

class memory_model_sct:public memory_model_baset
{
public:
  virtual void operator()(symex_target_equationt &equation);
  
protected:
  void program_order(symex_target_equationt &equation);
  void write_serialization_internal(symex_target_equationt &equation);
  void write_serialization_external(symex_target_equationt &equation);
};

#endif

