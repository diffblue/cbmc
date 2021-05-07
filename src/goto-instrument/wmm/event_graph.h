/*******************************************************************\

Module: graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// graph of abstract events

#ifndef CPROVER_GOTO_INSTRUMENT_WMM_EVENT_GRAPH_H
#define CPROVER_GOTO_INSTRUMENT_WMM_EVENT_GRAPH_H

#include <list>
#include <set>
#include <map>
#include <iosfwd>

#include <util/graph.h>
#include <util/invariant.h>

#include "abstract_event.h"
#include "data_dp.h"
#include "wmm.h"

class messaget;

typedef grapht<abstract_eventt> wmm_grapht;
typedef wmm_grapht::node_indext event_idt;

class event_grapht
{
public:
  /* critical cycle */
  class critical_cyclet final
  {
    typedef std::list<event_idt> data_typet;
    data_typet data;

    event_grapht &egraph;

    bool is_not_uniproc() const;
    bool is_not_weak_uniproc() const;

    std::string print_detail(const critical_cyclet &reduced,
      std::map<std::string, std::string> &map_id2var,
      std::map<std::string, std::string> &map_var2id) const;
    std::string print_name(const critical_cyclet &redyced,
      memory_modelt model) const;

    bool check_AC(
      data_typet::const_iterator s_it,
      const abstract_eventt &first,
      const abstract_eventt &second) const;
    bool check_BC(
      data_typet::const_iterator it,
      const abstract_eventt &first,
      const abstract_eventt &second) const;

  public:
    unsigned id;
    bool has_user_defined_fence;

    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::iterator iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::const_iterator const_iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef data_typet::value_type value_type;

    iterator begin() { return data.begin(); }
    const_iterator begin() const { return data.begin(); }
    const_iterator cbegin() const { return data.cbegin(); }

    iterator end() { return data.end(); }
    const_iterator end() const { return data.end(); }
    const_iterator cend() const { return data.cend(); }

    template <typename T>
    void push_front(T &&t) { data.push_front(std::forward<T>(t)); }

    template <typename T>
    void push_back(T &&t) { data.push_back(std::forward<T>(t)); }

    value_type &front() { return data.front(); }
    const value_type &front() const { return data.front(); }

    value_type &back() { return data.back(); }
    const value_type &back() const { return data.back(); }

    size_t size() const { return data.size(); }

    critical_cyclet(event_grapht &_egraph, unsigned _id)
      :egraph(_egraph), id(_id), has_user_defined_fence(false)
    {
    }

    void operator()(const critical_cyclet &cyc)
    {
      data.clear();
      for(auto it=cyc.data.cbegin();
          it!=cyc.data.cend();
          ++it)
        data.push_back(*it);
      has_user_defined_fence=cyc.has_user_defined_fence;
    }

    bool is_cycle()
    {
      /* size check */
      if(data.size()<4)
        return false;

      /* po order check */
      auto it=data.cbegin();
      auto n_it=it;
      ++n_it;
      for(; it!=data.cend() && n_it!=data.cend(); ++it, ++n_it)
      {
        if(egraph[*it].thread==egraph[*n_it].thread
          && !egraph.are_po_ordered(*it, *n_it))
          return false;
      }

      return true;
    }

    /* removes internal events (e.g. podWW Rfi gives podWR)
       from.hide_internals(&target) */
    void hide_internals(critical_cyclet &reduced) const;

    /// checks whether there is at least one pair which is unsafe (takes fences
    /// and dependencies into account), and adds the unsafe pairs in the set
    bool is_unsafe(memory_modelt model, bool fast=false);

    /* do not update the unsafe pairs set */
    bool is_unsafe_fast(memory_modelt model)
    {
      return is_unsafe(model, true);
    }

    void compute_unsafe_pairs(memory_modelt model)
    {
      is_unsafe(model);
    }

    bool is_unsafe_asm(memory_modelt model, bool fast=false);

    bool is_not_uniproc(memory_modelt model) const
    {
      if(model==RMO)
        return is_not_weak_uniproc();
      else
        return is_not_uniproc();
    }

    bool is_not_thin_air() const;

    /* pair of events in a cycle */
    struct delayt
    {
      event_idt first;
      event_idt second;
      bool is_po;

      explicit delayt(event_idt _first):
        first(_first), is_po(true)
      {
      }

      delayt(event_idt _first, event_idt _second):
        first(_first), second(_second), is_po(false)
      {
      }

      delayt(event_idt _first, event_idt _second, bool _is_po):
        first(_first), second(_second), is_po(_is_po)
      {
      }

      bool operator==(const delayt &other) const
      {
        return (is_po ? first==other.first :
                first==other.first && second==other.second);
      }

      bool operator<(const delayt &other) const
      {
        return (is_po ? first<other.first :
                first<other.first ||
                (first==other.first && second<other.second));
      }
    };

    std::set<delayt> unsafe_pairs;

    /* print events or ids in the cycles*/
    std::string print() const;
    std::string print_events() const;

    /* print outputs */
    std::string print_name(memory_modelt model) const
    {
      return print_name(*this, model);
    }
    std::string print_name(memory_modelt model, bool hide_internals) const
    {
      if(hide_internals)
      {
        critical_cyclet reduced(egraph, id);
        this->hide_internals(reduced);
        INVARIANT(!reduced.data.empty(), "reduced must not be empty");
        return print_name(reduced, model);
      }
      else
        return print_name(*this, model);
    }

    std::string print_unsafes() const;
    std::string print_output() const;
    std::string print_all(memory_modelt model,
      std::map<std::string, std::string> &map_id2var,
      std::map<std::string, std::string> &map_var2id,
      bool hide_internals) const;

    void print_dot(std::ostream &str,
      unsigned colour, memory_modelt model) const;

    bool operator<(const critical_cyclet &other) const
    {
      return data<other.data;
    }
  };

protected:
  /* graph contains po and com transitions */
  wmm_grapht po_graph;
  wmm_grapht com_graph;

  /* parameters limiting the exploration */
  unsigned max_var;
  unsigned max_po_trans;
  bool ignore_arrays;

  /* graph explorer (for each cycles collection) */
  class graph_explorert
  {
  public:
    virtual ~graph_explorert()
    {
    }

  protected:
    event_grapht &egraph;

    /* parameters limiting the exploration */
    unsigned max_var;
    unsigned max_po_trans;

    /* constraints for graph exploration */
    std::map<irep_idt, unsigned char> writes_per_variable;
    std::map<irep_idt, unsigned char> reads_per_variable;
    std::map<unsigned, unsigned char> events_per_thread;

    /* for thread and filtering in backtrack */
    virtual inline bool filtering(event_idt)
    {
      return false;
    }

    virtual inline std::list<event_idt>* order_filtering(
      std::list<event_idt>* order)
    {
      return order;
    }

    /* number of cycles met so far */
    unsigned cycle_nb;

    /* events in thin-air executions met so far */
    /* any execution blocked by thin-air is guaranteed
       to have all its events in this set */
    std::set<event_idt> thin_air_events;

    /* after the collection, eliminates the executions forbidden by an
       indirect thin-air */
    void filter_thin_air(std::set<critical_cyclet> &set_of_cycles);

  public:
    graph_explorert(
      event_grapht &_egraph,
      unsigned _max_var,
      unsigned _max_po_trans):
      egraph(_egraph),
      max_var(_max_var),
      max_po_trans(_max_po_trans),
      cycle_nb(0)
    {
    }

    /* structures for graph exploration */
    std::map<event_idt, bool> mark;
    std::stack<event_idt> marked_stack;
    std::stack<event_idt> point_stack;

    std::set<event_idt> skip_tracked;

    critical_cyclet extract_cycle(event_idt vertex,
      event_idt source, unsigned number_of_cycles);

    bool backtrack(std::set<critical_cyclet> &set_of_cycles,
      event_idt source,
      event_idt vertex,
      bool unsafe_met,
      event_idt po_trans,
      bool same_var_pair,
      bool lwsync_met,
      bool has_to_be_unsafe,
      irep_idt var_to_avoid,
      memory_modelt model);

    /* Tarjan 1972 adapted and modified for events + po-transitivity */
    void collect_cycles(
      std::set<critical_cyclet> &set_of_cycles,
      memory_modelt model);
  };

  /* explorer for thread */
  class graph_conc_explorert:public graph_explorert
  {
  protected:
    const std::set<event_idt> &filter;

  public:
    graph_conc_explorert(event_grapht &_egraph, unsigned _max_var,
      unsigned _max_po_trans, const std::set<event_idt> &_filter)
      :graph_explorert(_egraph, _max_var, _max_po_trans), filter(_filter)
    {
    }

    bool filtering(event_idt u)
    {
      return filter.find(u)==filter.end();
    }

    std::list<event_idt>* initial_filtering(std::list<event_idt>* order)
    {
      static std::list<event_idt> new_order;

      /* intersection */
      for(const auto &evt : *order)
        if(filter.find(evt)!=filter.end())
          new_order.push_back(evt);

      return &new_order;
    }
  };

  /* explorer for pairs collection a la Pensieve */
  class graph_pensieve_explorert:public graph_explorert
  {
  protected:
    std::set<event_idt> visited_nodes;
    bool naive;

    bool find_second_event(event_idt source);

  public:
    graph_pensieve_explorert(event_grapht &_egraph, unsigned _max_var,
      unsigned _max_po_trans)
      :graph_explorert(_egraph, _max_var, _max_po_trans), naive(false)
    {}

    void set_naive() {naive=true;}
    void collect_pairs();
  };

public:
  explicit event_grapht(messaget &_message):
    max_var(0),
    max_po_trans(0),
    ignore_arrays(false),
    filter_thin_air(true),
    filter_uniproc(true),
    message(_message)
  {
  }

  bool filter_thin_air;
  bool filter_uniproc;
  messaget &message;

  /* data dependencies per thread */
  std::map<unsigned, data_dpt> map_data_dp;

  /* orders */
  std::list<event_idt> po_order;
  std::list<event_idt> poUrfe_order;

  std::set<std::pair<event_idt, event_idt> > loops;

  event_idt add_node()
  {
    const event_idt po_no=po_graph.add_node();
    const event_idt com_no=com_graph.add_node();
    INVARIANT(po_no==com_no, "node added with same id in both graphs");
    return po_no;
  }

  grapht<abstract_eventt>::nodet &operator[](event_idt n)
  {
    return po_graph[n];
  }

  bool has_po_edge(event_idt i, event_idt j) const
  {
    return po_graph.has_edge(i, j);
  }

  bool has_com_edge(event_idt i, event_idt j) const
  {
    return com_graph.has_edge(i, j);
  }

  std::size_t size() const
  {
    return po_graph.size();
  }

  const wmm_grapht::edgest &po_in(event_idt n) const
  {
    return po_graph.in(n);
  }

  const wmm_grapht::edgest &po_out(event_idt n) const
  {
    return po_graph.out(n);
  }

  const wmm_grapht::edgest &com_in(event_idt n) const
  {
    return com_graph.in(n);
  }

  const wmm_grapht::edgest &com_out(event_idt n) const
  {
    return com_graph.out(n);
  }

  void add_po_edge(event_idt a, event_idt b)
  {
    assert(a!=b);
    assert(operator[](a).thread==operator[](b).thread);
    po_graph.add_edge(a, b);
    po_order.push_back(a);
    poUrfe_order.push_back(a);
  }

  void add_po_back_edge(event_idt a, event_idt b)
  {
    assert(a!=b);
    assert(operator[](a).thread==operator[](b).thread);
    po_graph.add_edge(a, b);
    po_order.push_back(a);
    poUrfe_order.push_back(a);
    loops.insert(std::pair<event_idt, event_idt>(a, b));
    loops.insert(std::pair<event_idt, event_idt>(b, a));
  }

  void add_com_edge(event_idt a, event_idt b)
  {
    assert(a!=b);
    com_graph.add_edge(a, b);
    poUrfe_order.push_back(a);
  }

  void add_undirected_com_edge(event_idt a, event_idt b)
  {
    assert(a!=b);
    add_com_edge(a, b);
    add_com_edge(b, a);
  }

  void remove_po_edge(event_idt a, event_idt b)
  {
    po_graph.remove_edge(a, b);
  }

  void remove_com_edge(event_idt a, event_idt b)
  {
    com_graph.remove_edge(a, b);
  }

  void remove_edge(event_idt a, event_idt b)
  {
    remove_po_edge(a, b);
    remove_com_edge(a, b);
  }

  /* copies the sub-graph G between begin and end into G', connects
     G.end with G'.begin, and returns G'.end */
  void explore_copy_segment(std::set<event_idt> &explored, event_idt begin,
    event_idt end) const;
  event_idt copy_segment(event_idt begin, event_idt end);

  /* to keep track of the loop already copied */
  std::set<std::pair<const abstract_eventt&, const abstract_eventt&>>
    duplicated_bodies;

  bool is_local(event_idt a)
  {
    return operator[](a).local;
  }

  /* a -po-> b  -- transitive */
  bool are_po_ordered(event_idt a, event_idt b)
  {
    if(operator[](a).thread!=operator[](b).thread)
      return false;

    /* if back-edge, a-po->b \/ b-po->a */
    if( loops.find(std::pair<event_idt, event_idt>(a, b))!=loops.end() )
      return true;

    // would be true if no cycle in po
    for(const auto &evt : po_order)
      if(evt==a)
        return true;
      else if(evt==b)
        return false;

    return false;
  }

  void clear()
  {
    po_graph.clear();
    com_graph.clear();
    map_data_dp.clear();
  }

  /* prints to graph.dot */
  void print_graph();
  void print_rec_graph(std::ofstream &file, event_idt node_id,
    std::set<event_idt> &visited);

  /* Tarjan 1972 adapted and modified for events + po-transitivity */
  void collect_cycles(std::set<critical_cyclet> &set_of_cycles,
    memory_modelt model,
    const std::set<event_idt> &filter)
  {
    graph_conc_explorert exploration(*this, max_var, max_po_trans, filter);
    exploration.collect_cycles(set_of_cycles, model);
  }

  void collect_cycles(std::set<critical_cyclet> &set_of_cycles,
    memory_modelt model)
  {
    graph_explorert exploration(*this, max_var, max_po_trans);
    exploration.collect_cycles(set_of_cycles, model);
  }

  void set_parameters_collection(
    unsigned _max_var=0,
    unsigned _max_po_trans=0,
    bool _ignore_arrays=false)
  {
    max_var = _max_var;
    max_po_trans = _max_po_trans;
    ignore_arrays = _ignore_arrays;
  }

  /* collects all the pairs of events with respectively at least one cmp,
     regardless of the architecture (Pensieve'05 strategy) */
  void collect_pairs()
  {
    graph_pensieve_explorert exploration(*this, max_var, max_po_trans);
    exploration.collect_pairs();
  }

  void collect_pairs_naive()
  {
    graph_pensieve_explorert exploration(*this, max_var, max_po_trans);
    exploration.set_naive();
    exploration.collect_pairs();
  }
};
#endif // CPROVER_GOTO_INSTRUMENT_WMM_EVENT_GRAPH_H
