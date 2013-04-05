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
  typedef std::vector<event_it> event_listt;
  
  // lists of reads and writes per address
  struct a_rect
  {
    event_listt reads, writes;
  };
  
  typedef std::map<irep_idt, a_rect> address_mapt;
  address_mapt address_map;
  
  void build_event_lists(symex_target_equationt &);
  
  // a per-thread numbering of the events
  typedef std::map<event_it, unsigned> numberingt;
  numberingt numbering;
  
  // program order
  bool po(event_it e1, event_it e2);

  // produce fresh symbols  
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(const std::string &prefix);
  
  // This gives us the choice symbol for a R-W pair;
  // built by the method below.
  typedef std::map<
    std::pair<event_it, event_it>, symbol_exprt> choice_symbolst;
  choice_symbolst choice_symbols;

  void read_from(symex_target_equationt &equation);
  
  // maps thread numbers to an event list
  typedef std::map<unsigned, event_listt> per_thread_mapt;
};

class memory_model_sct:public memory_model_baset
{
public:
  virtual void operator()(symex_target_equationt &equation);
  
protected:
  void program_order(symex_target_equationt &equation);
  void from_read(symex_target_equationt &equation);
  void write_serialization_internal(symex_target_equationt &equation);
  void write_serialization_external(symex_target_equationt &equation);
};

#endif

