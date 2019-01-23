/*******************************************************************\

Module: Instrumenter

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// Instrumenter

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_GOTO2GRAPH_H
#define CPROVER_GOTO_INSTRUMENT_WMM_GOTO2GRAPH_H

#include <map>

#include <util/graph.h>
#include <util/namespace.h>
#include <util/message.h>

#include <goto-programs/goto_model.h>

#include "event_graph.h"
#include "wmm.h"

class goto_modelt;
class value_setst;
class local_may_aliast;

class instrumentert
{
public:
  /* reference to goto-functions and symbol_table */
  namespacet ns;

protected:
  goto_functionst &goto_functions;

  /* alternative representation of graph (SCC) */
  std::map<event_idt, event_idt> map_vertex_gnode;
  wmm_grapht egraph_alt;

  unsigned unique_id;

  /* rendering options */
  bool render_po_aligned;
  bool render_by_file;
  bool render_by_function;

  bool inline local(const irep_idt &id);

  void inline add_instr_to_interleaving(
    goto_programt::instructionst::iterator it,
    goto_programt &interleaving);

  /* deprecated */
  bool is_cfg_spurious(const event_grapht::critical_cyclet &cyc);

  unsigned cost(const event_grapht::critical_cyclet::delayt &e);

  typedef std::set<event_grapht::critical_cyclet> set_of_cyclest;
  void inline instrument_all_inserter(
    const set_of_cyclest &set);
  void inline instrument_one_event_per_cycle_inserter(
    const set_of_cyclest &set);
  void inline instrument_one_read_per_cycle_inserter(
    const set_of_cyclest &set);
  void inline instrument_one_write_per_cycle_inserter(
    const set_of_cyclest &set);
  void inline instrument_minimum_interference_inserter(
    const set_of_cyclest &set);
  void inline instrument_my_events_inserter(
    const set_of_cyclest &set, const std::set<event_idt> &events);

  void inline print_outputs_local(
    const std::set<event_grapht::critical_cyclet> &set,
    std::ofstream &dot,
    std::ofstream &ref,
    std::ofstream &output,
    std::ofstream &all,
    std::ofstream &table,
    memory_modelt model,
    bool hide_internals);

  typedef std::set<goto_programt::instructiont::targett> target_sett;

  class cfg_visitort
  {
  protected:
    namespacet &ns;
    instrumentert &instrumenter;

    /* pointer to the egraph(s) that we construct */
    event_grapht &egraph;
    std::vector<std::set<event_idt>> &egraph_SCCs;
    wmm_grapht &egraph_alt;

    /* for thread marking (dynamic) */
    unsigned current_thread;
    unsigned coming_from;

    bool contains_shared_array(
      const irep_idt &function_id,
      goto_programt::const_targett targ,
      goto_programt::const_targett i_it,
      value_setst &value_sets
#ifdef LOCAL_MAY
      ,
      local_may_aliast local_may
#endif
      ) const; // NOLINT(whitespace/parens)

    /* transformers */
    void visit_cfg_thread() const;
    void visit_cfg_propagate(goto_programt::instructionst::iterator i_it);
    void visit_cfg_body(
      const irep_idt &function_id,
      const goto_programt &goto_program,
      goto_programt::const_targett i_it,
      loop_strategyt replicate_body,
      value_setst &value_sets
#ifdef LOCAL_MAY
      ,
      local_may_aliast &local_may
#endif
    ); // deprecated  NOLINT(whitespace/parens)
    void inline visit_cfg_backedge(goto_programt::const_targett targ,
      goto_programt::const_targett i_it);
    void inline visit_cfg_duplicate(
      const goto_programt &goto_program,
      goto_programt::const_targett targ,
      goto_programt::const_targett i_it);
    void visit_cfg_assign(
      value_setst &value_sets,
      const irep_idt &function_id,
      goto_programt::instructionst::iterator &i_it,
      bool no_dependencies
#ifdef LOCAL_MAY
      ,
      local_may_aliast &local_may
#endif
    ); // NOLINT(whitespace/parens)
    void visit_cfg_fence(goto_programt::instructionst::iterator i_it);
    void visit_cfg_skip(goto_programt::instructionst::iterator i_it);
    void visit_cfg_lwfence(goto_programt::instructionst::iterator i_it);
    void visit_cfg_asm_fence(goto_programt::instructionst::iterator i_it);
    void visit_cfg_function_call(value_setst &value_sets,
      goto_programt::instructionst::iterator i_it,
      memory_modelt model,
      bool no_dependenciess,
      loop_strategyt duplicate_body);
    void visit_cfg_goto(
      const irep_idt &function_id,
      const goto_programt &goto_program,
      goto_programt::instructionst::iterator i_it,
      /* forces the duplication of all the loops, with array or not
         otherwise, duplication of loops with array accesses only */
      loop_strategyt replicate_body,
      value_setst &value_sets
#ifdef LOCAL_MAY
      ,
      local_may_aliast &local_may
#endif
    ); // NOLINT(whitespace/parens)
    void visit_cfg_reference_function(irep_idt id_function);

 public:
    virtual ~cfg_visitort()
    {
    }

    unsigned max_thread;

    /* relations between irep and Reads/Writes */
    typedef std::multimap<irep_idt, event_idt> id2nodet;
    typedef std::pair<irep_idt, event_idt> id2node_pairt;
    id2nodet map_reads, map_writes;

    unsigned write_counter;
    unsigned read_counter;
    unsigned ws_counter;
    unsigned fr_rf_counter;

    /* previous nodes (fwd analysis) */
    typedef std::pair<event_idt, event_idt> nodet;
    typedef std::map<goto_programt::const_targett, std::set<nodet> >
      incoming_post;

    incoming_post in_pos;
    std::set<goto_programt::const_targett> updated;

    /* "next nodes" (bwd steps in fwd/bck analysis) */
    incoming_post out_pos;

    #define add_all_pos(it, target, source) \
    for(std::set<nodet>::const_iterator \
      it=(source).begin(); \
      it!=(source).end(); ++it) \
      (target).insert(*it);

    #ifdef CONTEXT_INSENSITIVE
    /* to keep track of the functions (and their start/end nodes) */
    std::stack<irep_idt> stack_fun;
    irep_idt cur_fun;
    std::map<irep_idt, std::set<nodet> > in_nodes, out_nodes;
    #endif

    /* current thread number */
    unsigned thread;

    /* dependencies */
    data_dpt data_dp;

    /* writes and reads to unknown addresses -- conservative */
    std::set<event_idt> unknown_read_nodes;
    std::set<event_idt> unknown_write_nodes;

    /* set of functions visited so far -- we don't handle recursive functions */
    std::set<irep_idt> functions_met;

    cfg_visitort(namespacet &_ns, instrumentert &_instrumenter)
    :ns(_ns), instrumenter(_instrumenter), egraph(_instrumenter.egraph),
      egraph_SCCs(_instrumenter.egraph_SCCs),
      egraph_alt(_instrumenter.egraph_alt)
    {
      write_counter = 0;
      read_counter = 0;
      ws_counter = 0;
      fr_rf_counter = 0;
      thread = 0;
      current_thread = 0;
      max_thread = 0;
      coming_from = 0;
    }

    void inline enter_function(const irep_idt &function_id)
    {
      if(functions_met.find(function_id) != functions_met.end())
        throw "sorry, doesn't handle recursive function for the moment";
      functions_met.insert(function_id);
    }

    void inline leave_function(const irep_idt &function_id)
    {
      functions_met.erase(function_id);
    }

    void inline visit_cfg(
      value_setst &value_sets,
      memory_modelt model,
      bool no_dependencies,
      loop_strategyt duplicate_body,
      const irep_idt &function_id)
    {
      /* ignore recursive calls -- underapproximation */
      try
      {
        /* forbids recursive function */
        enter_function(function_id);
        std::set<nodet> end_out;
        visit_cfg_function(
          value_sets,
          model,
          no_dependencies,
          duplicate_body,
          function_id,
          end_out);
        leave_function(function_id);
      }
      catch(const std::string &s)
      {
        instrumenter.message.warning() << s << messaget::eom;
      }
    }

    /// TODO: move the visitor outside, and inherit
    /// \param value_sets: Value_sets and options
    /// \param model: Memory model
    /// \param no_dependencies: Option to disable dependency analysis
    /// \param duplicate_body: Control which loop body segments should
    ///   be duplicated
    /// \param function_id: Function to analyse
    /// \param ending_vertex: Outcoming edges
    virtual void visit_cfg_function(
      value_setst &value_sets,
      memory_modelt model,
      bool no_dependencies,
      loop_strategyt duplicate_body,
      const irep_idt &function_id,
      std::set<nodet> &ending_vertex);

    bool inline local(const irep_idt &i);
  };

public:
  /* message */
  messaget &message;

  /* graph */
  event_grapht egraph;

  /* graph split into strongly connected components */
  std::vector<std::set<event_idt> > egraph_SCCs;

  /* critical cycles */
  std::set<event_grapht::critical_cyclet> set_of_cycles;

  /* critical cycles per SCC */
  std::vector<std::set<event_grapht::critical_cyclet> > set_of_cycles_per_SCC;
  unsigned num_sccs;

  /* map from function to begin and end of the corresponding part of the
     graph */
  typedef std::map<irep_idt, std::pair<std::set<event_idt>,
    std::set<event_idt> > > map_function_nodest;
  map_function_nodest map_function_graph;

  void print_map_function_graph() const
  {
    for(map_function_nodest::const_iterator it=map_function_graph.begin();
       it!=map_function_graph.end();
       ++it)
    {
       message.debug() << "FUNCTION " << it->first << ": " << messaget::eom;
       message.debug() << "Start nodes: ";
       for(std::set<event_idt>::const_iterator in_it=it->second.first.begin();
         in_it!=it->second.first.end();
         ++in_it)
         message.debug() << *in_it << " ";
       message.debug() << messaget::eom;
       message.debug() << "End nodes: ";
       for(std::set<event_idt>::const_iterator in_it=it->second.second.begin();
         in_it!=it->second.second.end();
         ++in_it)
         message.debug() << *in_it << " ";
       message.debug() << messaget::eom;
    }
  }

  /* variables to instrument, locations of variables to instrument on
     the cycles, and locations of all the variables on the critical cycles */
  /* TODO: those maps are here to interface easily with weak_mem.cpp,
     but a rewriting of weak_mem can eliminate them */
  std::set<irep_idt> var_to_instr;
  std::multimap<irep_idt, source_locationt> id2loc;
  std::multimap<irep_idt, source_locationt> id2cycloc;

  instrumentert(
    goto_modelt &_goto_model,
    messaget &_message):
    ns(_goto_model.symbol_table),
    goto_functions(_goto_model.goto_functions),
    render_po_aligned(true),
    render_by_file(false),
    render_by_function(false),
    message(_message),
    egraph(_message),
    num_sccs(0)
  {
  }

  /* abstracts goto-programs in abstract event graph, and computes
     the thread numbering and returns the max number */
  unsigned goto2graph_cfg(
    value_setst &value_sets,
    memory_modelt model,
    bool no_dependencies,
    /* forces the duplication, with arrays or not; otherwise, arrays only */
    loop_strategyt duplicate_body);

  /* collects directly all the cycles in the graph */
  void collect_cycles(memory_modelt model)
  {
    egraph.collect_cycles(set_of_cycles, model);
    num_sccs = 0;
  }

  /* collects the cycles in the graph by SCCs */
  void collect_cycles_by_SCCs(memory_modelt model);

  /* filters cycles spurious by CFG */
  void cfg_cycles_filter();

  /* sets parameters for collection, if required */
  void set_parameters_collection(
    unsigned _max_var = 0,
    unsigned _max_po_trans = 0,
    bool _ignore_arrays = false)
  {
    egraph.set_parameters_collection(_max_var, _max_po_trans, _ignore_arrays);
  }

  /* builds the relations between unsafe pairs in the critical cycles and
     instructions to instrument in the code */

  /* strategies for instrumentation */
  void instrument_with_strategy(instrumentation_strategyt strategy);
  void instrument_my_events(const std::set<event_idt> &events);

  /* retrieves events to filter in the instrumentation choice
     with option --my-events */
  static std::set<event_idt> extract_my_events();

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

#endif // CPROVER_GOTO_INSTRUMENT_WMM_GOTO2GRAPH_H
