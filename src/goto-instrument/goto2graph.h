/*******************************************************************\

Module: Instrumenter

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include <expr.h>
#include <hash_cont.h>
#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>
#include <graph.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <context.h>
#include "rw_set.h"

#include <cprover_prefix.h>
#include <prefix.h>
#include <i2string.h>

#include <cbmc/bmc.h>

#include "event_graph.h"
#include "fence.h"

class instrumentert
{
protected:
  /* reference to goto-functions and context */
  contextt& context;
  goto_functionst& goto_functions; 

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

  inline bool local(const irep_idt& id);

  void inline add_instr_to_interleaving (
    goto_programt::instructionst::iterator it,
    goto_programt& interleaving);
  bool is_cfg_spurious(const event_grapht::critical_cyclet& cyc);

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
    const set_of_cyclest& set,
    const std::set<unsigned>& events);

  void inline print_outputs_local(
    const std::set<event_grapht::critical_cyclet>& set,
    std::ofstream& dot,
    std::ofstream& ref,
    std::ofstream& output,
    weak_memory_modelt model);

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
  /* TO FIX: those maps are here to interface easily with weak_mem.cpp, 
     but a rewriting of weak_mem can eliminate them */
  std::set<irep_idt> var_to_instr;
  std::multimap<irep_idt,locationt> id2loc;
  std::multimap<irep_idt,locationt> id2cycloc;

  instrumentert(contextt& _context, goto_functionst& _goto_f)
    :context(_context),goto_functions(_goto_f),render_po_aligned(true),
      render_by_file(false),render_by_function(false)
  {
  }

  /* abstracts goto-programs in abstract event graph */
  void goto2graph(
    value_setst& value_sets,
    weak_memory_modelt model,
    bool no_dependencies);

  /* collects directly all the cycles in the graph */
  void collect_cycles(weak_memory_modelt model)
  {
    egraph.collect_cycles(set_of_cycles,model);
    num_sccs = 0;
  }

  /* collects the cycles in the graph by SCCs */
  void collect_cycles_by_SCCs(weak_memory_modelt model);

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
  void instrument_all();

  /* strategies for partial instrumentation */
  void instrument_one_event_per_cycle();
  void instrument_one_read_per_cycle();
  void instrument_one_write_per_cycle();
  void instrument_minimum_interference();
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
     - output.txt: names of the instructions in the code */
  void print_outputs(weak_memory_modelt model);
};
