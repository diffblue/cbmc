/*******************************************************************\

Module: Instrumenter

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#ifndef INSTRUMENTER_H
#define INSTRUMENTER_H

#include <map>

#include <util/graph.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/cfg.h>

#include "event_graph.h"
#include "wmm.h"

class symbol_tablet;
class goto_functionst;
class value_setst;

class instrumentert
{
protected:
  /* reference to goto-functions and symbol_table */
  namespacet ns;
  goto_functionst &goto_functions; 

  /* alternative representation of graph (SCC) */
  std::map<unsigned,unsigned> map_vertex_gnode;
  graph<abstract_eventt> egraph_alt;

  /* data dependencies per thread */
  std::map<unsigned,data_dpt> map_dependencies;

  unsigned unique_id;

  /* rendering options */
  bool render_po_aligned;
  bool render_by_file;
  bool render_by_function;

  bool inline local(const irep_idt& id);

  void inline add_instr_to_interleaving (
    goto_programt::instructionst::iterator it,
    goto_programt& interleaving);

  /* deprecated */
  bool is_cfg_spurious(const event_grapht::critical_cyclet& cyc);

  unsigned cost(const event_grapht::critical_cyclet::delayt& e);

  typedef std::set<event_grapht::critical_cyclet> set_of_cyclest;
  void inline instrument_all_inserter(
    const set_of_cyclest& set);
  void inline instrument_one_event_per_cycle_inserter(
    const set_of_cyclest& set);
  void inline instrument_one_read_per_cycle_inserter(
    const set_of_cyclest& set);
  void inline instrument_one_write_per_cycle_inserter(
    const set_of_cyclest& set);
  void inline instrument_minimum_interference_inserter(
    const set_of_cyclest& set);
  void inline instrument_my_events_inserter(
    const set_of_cyclest& set, const std::set<unsigned>& events);

  void inline print_outputs_local(
    const std::set<event_grapht::critical_cyclet>& set,
    std::ofstream& dot,
    std::ofstream& ref,
    std::ofstream& output,
    std::ofstream& all,
    std::ofstream& table,
    memory_modelt model,
    bool hide_internals);

public:
  /* forward traversal of program */
  typedef std::list<unsigned> nodest;
  struct thread_eventst
  {
    nodest reads;
    nodest writes;
    nodest fences;
  };

  struct event_datat
  {
    std::map<unsigned, thread_eventst> events;
    std::set<goto_programt::const_targett> use_events_from;
  };

  /* per-thread control flow graph only, no inter-thread edges */
  typedef cfg_baset<event_datat> cfgt;
  cfgt cfg;

protected:
  /* for thread marking (dynamic) */
  unsigned max_thread;
  /* current thread number */
  unsigned thread;

  /* relations between irep and Reads/Writes */
  typedef std::multimap<irep_idt,unsigned> id2nodet;
  typedef std::pair<irep_idt,unsigned> id2node_pairt;
  id2nodet map_reads, map_writes;

  /* dependencies */
  data_dpt data_dp;

  /* set of functions visited so far -- we don't handle recursive functions */
  std::set<irep_idt> functions_met;

  /* transformers */
  void extract_events_rw(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies,
    goto_programt::const_targett target,
    thread_eventst &dest);
  void extract_events_fence(
    memory_modelt model,
    goto_programt::const_targett target,
    thread_eventst &dest);
  void extract_events(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies,
    cfgt::entryt &cfg_entry);

  void add_po_edges(
    const nodest &from_events,
    const unsigned event_node,
    const unsigned event_gnode,
    const bool is_backward);
  void add_po_edges(
    const unsigned thread_nr,
    const cfgt::entryt &from,
    const cfgt::entryt &to,
    const unsigned event_node,
    const unsigned event_gnode);
  void add_po_edges(
    const cfgt::entryt &cfg_entry,
    const unsigned thread_nr,
    const unsigned event_node);
  void add_po_edges(
    const cfgt::entryt &cfg_entry,
    const unsigned thread_nr,
    const thread_eventst &thread_events);
  void add_edges_assign(
    const cfgt::entryt &cfg_entry,
    const thread_eventst &thread_events);
  void add_com_edges(
    const cfgt::entryt &cfg_entry,
    const thread_eventst &thread_events);
  void add_edges(
    const cfgt::entryt &cfg_entry,
    const unsigned thread_nr,
    const thread_eventst &thread_events);

public:
  /* graph */
  event_grapht egraph;

  /* graph split into strongly connected components */
  std::vector<std::set<unsigned> > egraph_SCCs;

  /* critical cycles */
  std::set<event_grapht::critical_cyclet> set_of_cycles;

  /* critical cycles per SCC */
  std::vector<std::set<event_grapht::critical_cyclet> > set_of_cycles_per_SCC;
  unsigned num_sccs;

  /* variables to instrument, locations of variables to instrument on 
     the cycles, and locations of all the variables on the critical cycles */
  /* TODO: those maps are here to interface easily with weak_mem.cpp, 
     but a rewriting of weak_mem can eliminate them */
  std::set<irep_idt> var_to_instr;
  std::multimap<irep_idt,locationt> id2loc;
  std::multimap<irep_idt,locationt> id2cycloc;

  instrumentert(symbol_tablet& _symbol_table, goto_functionst& _goto_f)
    :ns(_symbol_table), goto_functions(_goto_f), render_po_aligned(true), 
      render_by_file(false), render_by_function(false),
    max_thread(0),
    thread(0),
    write_counter(0),
    read_counter(0)
  {
  }

  /* abstracts goto-programs in abstract event graph, and computes
     the thread numbering and returns the max number */
  unsigned write_counter;
  unsigned read_counter;

  void forward_traverse_once(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies,
    goto_programt::const_targett target);
  void forward_traverse_once(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies);

  void propagate_events_in_po();

  void add_edges();

  unsigned build_event_graph(
    value_setst& value_sets,
    memory_modelt model,
    bool no_dependencies);

  /* collects directly all the cycles in the graph */
  void collect_cycles(memory_modelt model)
  {
    egraph.collect_cycles(set_of_cycles,model);
    num_sccs = 0;
  }

  /* collects the cycles in the graph by SCCs */
  void collect_cycles_by_SCCs(memory_modelt model);

  /* filters cycles spurious by CFG */
  void cfg_cycles_filter();

  /* sets parameters for collection, if required */
  void set_parameters_collection(unsigned _max_var = 0,
    unsigned _max_po_trans = 0)
  {
    egraph.set_parameters_collection(_max_var,_max_po_trans);
  }

  /* builds the relations between unsafe pairs in the critical cycles and
     instructions to instrument in the code */

  /* strategies for instrumentation */
  void instrument_with_strategy(instrumentation_strategyt strategy);
  void instrument_my_events(const std::set<unsigned>& events);

  /* sets rendering options */
  void set_rendering_options(bool aligned, bool file, bool function)
  {
    render_po_aligned = aligned;
    render_by_file = file;
    render_by_function = function;
    assert(!render_by_file || !render_by_function);
  }

  /* prints outputs:
     - cycles.dot: graph of the instrumented cycles  
     - ref.txt: names of the instrumented cycles
     - output.txt: names of the instructions in the code 
     - all.txt: all */
  void print_outputs(memory_modelt model, bool hide_internals);
};

#endif
