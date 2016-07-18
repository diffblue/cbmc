/*******************************************************************\

Module: Lock graph Analysis (context-sensitive)

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOCK_GRAPH_CS_H
#define CPROVER_POINTER_ANALYSIS_LOCK_GRAPH_CS_H

#include "non_concurrent.h"
#include "lock_set_analysis_cs.h"
#include "lock_graph_cs.h"

class lock_graph_analysis_cst;

class lock_graph_cs_domaint : public ai_cs_domain_baset
{
public:

  inline bool merge(const lock_graph_cs_domaint &other, 
		    locationt from, locationt to, const ai_cs_stackt &stack) 
    { return false; }

  /*
  bool merge_shared(
    const lock_graph_cs_domaint &other,
    locationt from,
    locationt to,
    const namespacet &ns)
  {
    return merge(other, from, to);
  }
  */
  
  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
  }

  virtual void transform(
    locationt from_l,
    locationt to_l,
    const ai_cs_stackt &stack,
    ai_cs_baset &ai,
    const namespacet &ns);

};


class xmlt;

class lock_graph_analysis_cst:
  public ai_cst<lock_graph_cs_domaint>
{
public:
  typedef ai_cst<lock_graph_cs_domaint> baset;

  lock_graph_analysis_cst(
    in_loopt& _in_loop,
    non_concurrentt& _non_concurrent,
    may_lock_set_analysis_cst &_lock_set_analysis)
  :
    ai_cst<lock_graph_cs_domaint>(_in_loop),
    non_concurrent(_non_concurrent),
    lock_set_analysis(_lock_set_analysis),
    cycle_visitor(*this)
   {
   }

  lock_graph_analysis_cst(
    in_loopt& _in_loop,
    non_concurrentt& _non_concurrent,
    may_lock_set_analysis_cst &_lock_set_analysis,
    stack_numberingt &stack_numbering)
  :
    ai_cst<lock_graph_cs_domaint>(_in_loop, stack_numbering),
    non_concurrent(_non_concurrent),
    lock_set_analysis(_lock_set_analysis),
    cycle_visitor(*this)
   {
   }


  virtual ~lock_graph_analysis_cst() {}

  void detect_deadlocks();

  // overloading
  virtual void output(const namespacet &ns, const goto_functionst &goto_functions,
		      std::ostream &out) const
  {
    graph.output(ns, out);
  }
  virtual void convert(const namespacet &ns, const goto_functionst &goto_functions,
		       xmlt &dest)
  {
    graph.convert(ns, dest);
  }
  
  void output_deadlocks(const namespacet &ns, std::ostream &out);
  void convert_deadlocks(const namespacet &ns, xmlt &dest);

  void show_deadlocks(
    const namespacet &ns,
    ui_message_handlert::uit ui);

  non_concurrentt& non_concurrent;
  may_lock_set_analysis_cst &lock_set_analysis;

  lock_graph_cst graph;

  struct statisticst {
    std::set<ai_cs_stackt> threads;
    unsigned no_lock_operations;
    unsigned no_indet_lock_operations;
    unsigned long size_largest_lock_set;
    unsigned no_non_concurrent_checks;
    unsigned no_cycles;

    statisticst() :
      no_lock_operations(0),
      no_indet_lock_operations(0),
      size_largest_lock_set(0),
      no_non_concurrent_checks(0),
      no_cycles(0) {}
  };
  statisticst statistics;

  virtual void show(
    const namespacet &ns,
    ui_message_handlert::uit ui,
    const goto_functionst &goto_functions)
  {
    show_analysist::show(ns, ui, goto_functions);
    if(ui==ui_message_handlert::PLAIN)
      output_statistics1(std::cout);
  }
  
  void output_statistics1(std::ostream &out);
  void output_statistics2(std::ostream &out);

protected:
  typedef lock_graph_cst::pathst deadlockst;

  deadlockst potential_deadlocks;

  class cycle_visitort : public lock_graph_cst::cycle_visitort
  {
    lock_graph_analysis_cst &super;
   public:
    cycle_visitort(lock_graph_analysis_cst &_super)
      : super(_super)
    {}

    virtual bool visit(const lock_graph_cst::patht &cycle, bool &filter_out);
  };
  cycle_visitort cycle_visitor;

  bool check_cycle(const lock_graph_cst::patht &cycle);
};


#endif
