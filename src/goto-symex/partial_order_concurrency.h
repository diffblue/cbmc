/*******************************************************************\

Module: Add constraints to equation encoding partial orders on events

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_PARTIAL_ORDER_CONCURRENCY_H
#define CPROVER_PARTIAL_ORDER_CONCURRENCY_H

#include <util/message.h>

#include "symex_target_equation.h"

class partial_order_concurrencyt:public messaget
{
public:
  explicit partial_order_concurrencyt(const namespacet &_ns);
  virtual ~partial_order_concurrencyt();

  typedef symex_target_equationt::SSA_stept eventt;
  typedef symex_target_equationt::SSA_stepst eventst;
  typedef eventst::const_iterator event_it;

  // the name of a clock variable for a shared read/write
  typedef enum {
    AX_SC_PER_LOCATION=1,
    AX_NO_THINAIR=2,
    AX_OBSERVATION=4,
    AX_PROPAGATION=8
  } axiomt;

  static irep_idt rw_clock_id(
    event_it e,
    axiomt axiom=AX_PROPAGATION);
  
protected:
  const namespacet &ns;

  typedef std::vector<event_it> event_listt;
  
  // lists of reads and writes per address
  struct a_rect
  {
    event_listt reads, writes;
  };
  
  typedef std::map<irep_idt, a_rect> address_mapt;
  address_mapt address_map;
  
  void build_event_lists(symex_target_equationt &);
  void add_init_writes(symex_target_equationt &);
  
  // a per-thread numbering of the events
  typedef std::map<event_it, unsigned> numberingt;
  numberingt numbering;  
  
  // produces the symbol ID for an event
  static inline irep_idt id(event_it event)
  {
    return event->ssa_lhs.get_identifier();
  }
  
  // produces an address ID for an event
  inline irep_idt address(event_it event) const
  {
    return event->original_lhs_object.get_identifier();
  }

  // produce a clock symbol for some event
  typet clock_type;
  symbol_exprt clock(event_it e, axiomt axiom);
  void build_clock_type(const symex_target_equationt &);

  // preprocess and add a constraint to equation
  void add_constraint(
    symex_target_equationt &equation,
    const exprt &cond,
    const std::string &msg,
    const symex_targett::sourcet &source) const;
  
  // the partial order constraint for two events
  exprt before(event_it e1, event_it e2, unsigned axioms);
  virtual exprt before(event_it e1, event_it e2)=0;

  // is it an assignment for a shared variable?
  bool is_shared_write(event_it e) const;

  // is it a read from a shared variable?
  bool is_shared_read(event_it e) const;
  
  // is this a spawn?
  static inline bool is_spawn(event_it e)
  {
    return e->is_spawn();
  }

  // is this a fence?
  static inline bool is_memory_barrier(event_it e)
  {
    return e->is_memory_barrier();
  }
};

#if 0
#include <list>
#include <map>
#include <vector>
#include <string>

#include "abstract_event_structure.h"

class memory_model_baset;

class numbered_evtst
{
  typedef abstract_eventt evtt;

public:
  typedef std::vector<evtt const*> ordered_evtst;
  typedef ordered_evtst::const_iterator const_iterator;
  typedef std::map<evtt const*, ordered_evtst::size_type> ordered_evts_mapt;

  void add_event(const evtt &evt)
  {
    const ordered_evtst::size_type offset=ordered_evts.size();
    ordered_evts.push_back(&evt);
    if(!ordered_evts_map.insert(std::make_pair(&evt, offset)).second)
      assert(false);
    assert(ordered_evts.size()==ordered_evts_map.size());

    if(evt.direction==evtt::D_SYNC ||
        evt.direction==evtt::D_LWSYNC)
      barriers.insert(barriers.end(), offset);
  }

  void add_events(const_iterator first, const_iterator last)
  {
    ordered_evts.reserve(ordered_evts.size()+last-first);
    for( ; first!=last; ++first)
      add_event(**first);
  }

  const_iterator begin() const
  {
    return ordered_evts.begin();
  }

  const_iterator end() const
  {
    return ordered_evts.end();
  }

  const_iterator find(const evtt &evt) const
  {
    ordered_evts_mapt::const_iterator entry=ordered_evts_map.find(&evt);
    if(entry==ordered_evts_map.end())
      return end();

    return ordered_evts.begin()+entry->second;
  }

  std::list<const_iterator> barriers_after(const evtt &evt) const
  {
    const_iterator entry=find(evt);
    if(entry==end())
      return std::list<const_iterator>();

    std::list<const_iterator> ret;
    ordered_evtst::size_type offset=entry-begin();
    for(std::set<ordered_evtst::size_type>::const_iterator
        lb=barriers.lower_bound(offset);
        lb!=barriers.end();
        ++lb)
      ret.push_back(ordered_evts.begin()+*lb);

    return ret;
  }

  std::list<const_iterator> barriers_before(const evtt &evt) const
  {
    const_iterator entry=find(evt);
    if(entry==end())
      return std::list<const_iterator>();

    std::list<const_iterator> ret;
    ordered_evtst::size_type offset=entry-begin();
    for(std::set<ordered_evtst::size_type>::const_iterator
        ub=barriers.begin();
        ub!=barriers.end() && *ub<=offset;
        ++ub)
      ret.push_back(ordered_evts.begin()+*ub);

    return ret;
  }

private:
  ordered_evtst ordered_evts;
  ordered_evts_mapt ordered_evts_map;
  std::set<ordered_evtst::size_type> barriers;
};

class partial_order_concurrencyt
{
public:
  // the is-acyclic checks
  typedef enum {
    AC_UNIPROC=0,
    AC_THINAIR=1,
    AC_GHB=2,
    AC_PPC_WS_FENCE=3,
    AC_N_AXIOMS=4
  } acyclict;

  typedef abstract_eventt evtt;
  typedef std::map<evtt const*, std::map<evtt const*, exprt> > adj_matrixt;
  typedef adj_matrixt adj_matricest[AC_N_AXIOMS];
  typedef std::list<evtt const*> per_valuet;
  typedef std::map<irep_idt, per_valuet> per_address_mapt;
  typedef std::vector<numbered_evtst> numbered_per_thread_evtst;

  partial_order_concurrencyt(
      memory_model_baset &_memory_model,
      symex_target_equationt &_target,
      const namespacet &_ns,
      messaget &_message);

  void init(const abstract_events_in_program_ordert &abstract_events_in_po);
  void add_atomic_sections();

  // collect all partial orders
  void add_program_order(adj_matricest &po);
  void add_read_from(adj_matricest &rf);
  void add_write_serialisation(adj_matricest &ws);
  void add_from_read(
      const adj_matricest &rf,
      const adj_matricest &ws,
      adj_matricest &fr);
  void add_barriers(
      const adj_matricest &po,
      const adj_matricest &rf,
      const adj_matricest &fr);

  void acyclic();

  // steps as used in PLDI Power model
#  define S_COMMIT 0
#  define S_R_REQ 1
#  define S_S_ACK 1
#  define S_PROP(t) ((t+1)<<1)
  symbol_exprt clock(
      const acyclict check,
      const evtt &n,
      const unsigned step) const;
  symbol_exprt clock(
      const acyclict check,
      const evtt &n,
      const unsigned step,
      const evtt::event_dirt other_dir) const;

  symbol_exprt fresh_nondet_bool();
  void add_constraint(
      exprt &expr,
      const guardt &guard,
      const symex_targett::sourcet &source,
      const std::string &po_name);
  void add_atomic_sections(const acyclict check);
  void add_partial_order_constraint(
      const acyclict check,
      const std::string &po_name,
      const evtt &n1,
      const evtt &n2,
      const exprt& cond);
  void add_partial_order_constraint(
      const acyclict check,
      const std::string &po_name,
      const evtt &n1,
      const unsigned n1_step,
      const evtt::event_dirt n1_o_d,
      const evtt &n2,
      const unsigned n2_step,
      const evtt::event_dirt n2_o_d,
      const exprt& cond);

  const evtt* first_of(const evtt &e1, const evtt &e2) const;
  const numbered_evtst& get_thread(const evtt &e) const;
  const numbered_per_thread_evtst& get_all_threads() const
  {
    return per_thread_evt_no;
  }

  const namespacet& get_ns() const { return ns; }
  messaget& get_message() { return message; }
  std::map<std::string, unsigned> num_concurrency_constraints;

private:
  memory_model_baset &memory_model;
  symex_target_equationt &target;
  const namespacet &ns;
  messaget &message;

  // collect all reads and writes to each address
  per_address_mapt reads_per_address, writes_per_address;

  // initialisation events for uninitialised globals
  std::map<irep_idt, evtt> init_val;

  // constraints added to the formula
  const std::string prop_var;
  unsigned prop_cnt;

  // number events according to po per thread, including parents
  numbered_per_thread_evtst per_thread_evt_no;

  // map between events and (symbolic) integers
  typet node_type;
  std::map<evtt const*, unsigned> barrier_id;
  inline symbol_exprt node_symbol(
      const evtt &evt,
      const std::string &prefix) const;
  std::vector<std::pair<symbol_exprt, symbol_exprt> > atomic_section_bounds[AC_N_AXIOMS];

  std::list<exprt> acyclic_constraints[AC_N_AXIOMS];
  static std::string check_to_string(const acyclict check);

  // map point-wise order to a single Boolean symbol
  typedef std::pair<evtt const*, std::pair<unsigned, evtt::event_dirt> > evt_dir_pairt;
  typedef std::map<std::pair<evt_dir_pairt, evt_dir_pairt>,
          symbol_exprt> pointwise_mapt;
  pointwise_mapt edge_cache[AC_N_AXIOMS];
  typedef std::map<evtt const*,
          std::list<std::pair<evtt const*, std::pair<exprt, std::string> > > >
            edge_to_guardt;
  edge_to_guardt edge_to_guard[AC_N_AXIOMS];

  void add_sub_clock_rules();

  typedef std::map<std::pair<irep_idt, irep_idt>, symbol_exprt> clock_mapt;
  clock_mapt clock_constraint_cache;
  symbol_exprt add_clock_constraint(
      const symbol_exprt &n1_sym,
      const symbol_exprt &n2_sym,
      const symex_targett::sourcet &source,
      const std::string &po_name);
  const symbol_exprt &get_partial_order_constraint(
      const acyclict check,
      const std::string &po_name,
      const evtt &n1,
      const unsigned n1_step,
      const evtt::event_dirt n1_o_d,
      const evtt &n2,
      const unsigned n2_step,
      const evtt::event_dirt n2_o_d);
  void build_partial_order_constraint(
      const acyclict check,
      const std::string &po_name,
      const evtt &n1,
      const unsigned n1_step,
      const evtt::event_dirt n1_o_d,
      const evtt &n2,
      const unsigned n2_step,
      const evtt::event_dirt n2_o_d,
      symbol_exprt &dest);

  // debugging output
  std::string event_to_string(const evtt &evt) const;
  void print_graph(
      const adj_matrixt &graph,
      const std::string &edge_label,
      namespacet const& ns) const;
};
#endif

#endif
