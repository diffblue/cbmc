/*******************************************************************\

Module: graph of abstract events

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#ifndef EVENT_GRAPH_H
#define EVENT_GRAPH_H

#include <list>
#include <set>

#include <util/location.h>
#include <util/graph.h>

#include <iostream>
#include <fstream>

#ifndef MEMORY_MODEL
#define MEMORY_MODEL
typedef enum {TSO, PSO, RMO, Power} weak_memory_modelt;
#endif 

/* abstract event */
class abstract_eventt:public graph_nodet<empty_nodet>
{
protected:
  bool unsafe_pair_lwfence_param(const abstract_eventt& next,
    weak_memory_modelt model, bool lwsync_met) const;

public:
  typedef enum {Write, Read, Fence, Lwfence} operationt;

  operationt operation;
  unsigned thread;
  irep_idt variable;
  unsigned id;
  locationt location;
  bool local;

  abstract_eventt()
  {
  }

  abstract_eventt(operationt _op, unsigned _th, irep_idt _var, 
    unsigned _id, locationt _loc, bool _local)
    :operation(_op),thread(_th),variable(_var),id(_id),location(_loc),local(_local)
  {
  }

  inline bool operator==(const abstract_eventt& other)
  {
    return (id == other.id);
  }

  inline bool operator<(const abstract_eventt& other) const
  {
    return (id < other.id);
  }

  inline void operator()(const abstract_eventt& other)
  {
    operation = other.operation;
    thread = other.thread;
    variable = other.variable;
    id = other.id;
    location = other.location;
    local = other.local;
  }

  /* checks the safety of the pair locally (i.e., w/o taking fences
     or dependencies into account -- use is_unsafe on the whole
     critical cycle for this) */
  bool unsafe_pair(const abstract_eventt& next, weak_memory_modelt model) const
  {
    return unsafe_pair_lwfence_param(next,model,false);
  }

  bool unsafe_pair_lwfence(const abstract_eventt& next, weak_memory_modelt model) const
  {
    return unsafe_pair_lwfence_param(next,model,true);
  }

  std::string get_operation() const
  {
    switch(operation)
    {
      case Write: return "W";
      case Read: return "R";
      case Fence: return "F";
      case Lwfence: return "f";
      default: return "?";
    }
  }
};


/* data dependencies */
class data_dpt
{
public:
  typedef std::pair<irep_idt, locationt> datat;

  /* class of data equivalence */
  class data_classt:public std::set<datat>
  {
  public:
    inline void operator()(const data_classt& other)
    {
      for(iterator it=other.begin(); it!=other.end(); it++)
        insert(*it);
    }
  };

  std::set<data_classt> dependencies;

public:
  /* add this dependency in the structure */
  void dp_analysis(const abstract_eventt& read, const abstract_eventt& write);
  void dp_analysis(const datat& read, bool local_read, const datat& write, bool local_write);
  /* are these two events with a data dependency ? */
  bool dp(const abstract_eventt& e1, const abstract_eventt& e2) const;
  void dp_merge();
  void print();
};


/* graph of abstract events */
class event_grapht
{
public:
  /* critical cycle */
  class critical_cyclet:public std::list<unsigned>
  {
  protected:
    event_grapht& egraph;

  public:
    unsigned id;

    critical_cyclet(event_grapht& _egraph, unsigned _id)
      :egraph(_egraph),id(_id)
    {
    }

    void operator()(const critical_cyclet& cyc)
    {
      clear();
      for(const_iterator it=cyc.begin(); it!=cyc.end(); it++)
        push_back(*it);
    }
    
    bool is_cycle()
    {
      if(size()<4)
        return false;

      for(iterator it=begin(); it!=end() && ++it!=end(); it++)
      {
        iterator s_it = it;
        --it;
        if(egraph[*it].thread==egraph[*s_it].thread 
          && !egraph.are_po_ordered(*it,*s_it))
          return false;
      }

      return !(egraph[back()].thread==egraph[front()].thread
        && !egraph.are_po_ordered(back(),front()));
    }

    /* checks whether there is at leat one pair which is unsafe 
       (takes fences and dependencies into account), and adds
       the unsafe pairs in the set */
    bool is_unsafe(weak_memory_modelt model, bool fast = false);

    /* do not update the unsafe pairs set */
    bool is_unsafe_fast(weak_memory_modelt model)
    {
      return is_unsafe(model,true);
    }

    void compute_unsafe_pairs(weak_memory_modelt model)
    {
      is_unsafe(model);
    }

    bool is_not_uniproc() const;
    bool is_not_thin_air() const;

    /* pair of events in a cycle */
    class delayt
    {
    public:
      unsigned first;
      unsigned second;
      bool is_po;

      delayt(unsigned _first)
        :first(_first),is_po(true)
      {
      }

      delayt(unsigned _first, unsigned _second)
        :first(_first),second(_second),is_po(false)
      {
      }

      delayt(unsigned _first, unsigned _second, bool _is_po)
        :first(_first),second(_second),is_po(_is_po)
      {
      }

      inline bool operator==(const delayt& other) const
      {
        return (is_po ? first==other.first
          : first==other.first&&second==other.second);
      }

      inline bool operator<(const delayt& other) const
      {
        return (is_po ? first<other.first
          : first<other.first||(first==other.first&&second<other.second));
      }
    };

    std::set<delayt> unsafe_pairs;

    /* print events or ids in the cycles*/    
    std::string print() const;
    std::string print_events() const;

    /* print outputs */
    std::string print_name(weak_memory_modelt model) const;
    std::string print_output() const;
    void print_dot(std::ofstream& str, 
      unsigned colour, weak_memory_modelt model) const;

    inline bool operator<(const critical_cyclet& other) const
    {
      return ( ((std::list<unsigned>) *this) < (std::list<unsigned>)other);
    }
  };

protected:
  /* graph contains po and com transitions */
  graph<abstract_eventt> po_graph;
  graph<abstract_eventt> com_graph;

  /* parameters limiting the exploration */
  unsigned max_var;
  unsigned max_po_trans;

  /* graph explorer (for each cycles collection) */
  class graph_explorert
  {
  protected:
    event_grapht& egraph;

    /* parameters limiting the exploration */
    unsigned max_var;
    unsigned max_po_trans;

    /* constraints for graph exploration */
    std::map<irep_idt,unsigned char> writes_per_variable;
    std::map<irep_idt,unsigned char> reads_per_variable;
    std::map<unsigned,unsigned char> events_per_thread;

    /* for thread and filtering in backtrack */
    virtual inline bool filtering(unsigned u)
    {
      return false;
    }

    virtual inline std::list<unsigned>* order_filtering(
      std::list<unsigned>* order)
    {
      return order;
    }

    /* number of cycles met so far */
    unsigned cycle_nb;

  public:
    graph_explorert(event_grapht& _egraph, unsigned _max_var, 
      unsigned _max_po_trans)
      :egraph(_egraph),max_var(_max_var),
        max_po_trans(_max_po_trans),cycle_nb(0)
    {
    }

    /* structures for graph exploration */
    std::map<unsigned,bool> mark;
    std::stack<unsigned> marked_stack;
    std::stack<unsigned> point_stack;

    critical_cyclet extract_cycle(unsigned vertex, 
      unsigned source, unsigned number_of_cycles);

    bool backtrack(std::set<critical_cyclet>& set_of_cycles,
      unsigned source,
      unsigned vertex,
      bool unsafe_met,
      unsigned po_trans,
      bool same_var_pair,
      bool lwsync_met,
      weak_memory_modelt model);

    /* Tarjan 1972 adapted and modified for events + po-transitivity */
    void collect_cycles(
      std::set<critical_cyclet>& set_of_cycles,
      weak_memory_modelt model);
  };

  /* explorer for thread */
  class graph_conc_explorert:public graph_explorert
  {
  protected:
    const std::set<unsigned>& filter;

  public:
    graph_conc_explorert(event_grapht& _egraph, unsigned _max_var,
      unsigned _max_po_trans, const std::set<unsigned>& _filter)
      :graph_explorert(_egraph,_max_var,_max_po_trans),filter(_filter)
    {
    }

    inline bool filtering(unsigned u)
    {
      return filter.find(u)==filter.end();
    }

    inline std::list<unsigned>* initial_filtering(std::list<unsigned>* order)
    {
      static std::list<unsigned> new_order;

      /* intersection */
      for(std::list<unsigned>::iterator it=order->begin();it!=order->end();it++)
        if(filter.find(*it)!=filter.end())
          new_order.push_back(*it);

      return &new_order;
    }
  };

public:
  /* data dependencies per thread */
  std::map<unsigned,data_dpt> map_data_dp;

  /* orders */
  std::list<unsigned> po_order;
  std::list<unsigned> poUrfe_order;

  unsigned add_node()
  {
    const unsigned po_no = po_graph.add_node();
    const unsigned com_no = com_graph.add_node();
    assert(po_no == com_no);
    return po_no;
  }

  inline graph<abstract_eventt>::nodet &operator[](unsigned n)
  {
    return po_graph[n];
  } 

  bool has_po_edge(unsigned i, unsigned j) const
  {
    return po_graph.has_edge(i,j);
  }

  bool has_com_edge(unsigned i, unsigned j) const
  {
    return com_graph.has_edge(i,j);
  }

  inline unsigned size() const
  {
    return po_graph.size();
  }

  inline const graph<abstract_eventt>::edgest &po_in(unsigned n) const
  {
    return po_graph.in(n);
  }

  inline const graph<abstract_eventt>::edgest &po_out(unsigned n) const
  {
    return po_graph.out(n);
  }

  inline const graph<abstract_eventt>::edgest &com_in(unsigned n) const
  {
    return com_graph.in(n);
  }

  inline const graph<abstract_eventt>::edgest &com_out(unsigned n) const
  {
    return com_graph.out(n);
  }

  void add_po_edge(unsigned a, unsigned b)
  {
    po_graph.add_edge(a,b);
    po_order.push_back(a);
    poUrfe_order.push_back(a);
  }

  void add_com_edge(unsigned a, unsigned b)
  {
    com_graph.add_edge(a,b);
    poUrfe_order.push_back(a);
  }

  void add_undirected_com_edge(unsigned a, unsigned b)
  {
    add_com_edge(a,b);
    add_com_edge(b,a);
  }

  void remove_po_edge(unsigned a, unsigned b)
  {
    po_graph.remove_edge(a,b);
  }

  void remove_com_edge(unsigned a, unsigned b)
  {
    com_graph.remove_edge(a,b);
  }

  void remove_edge(unsigned a, unsigned b)
  {
    remove_po_edge(a,b);
    remove_com_edge(a,b);
  }

  bool is_local(unsigned a)
  {
    return operator[](a).local;
  }

  /* a -po-> b */
  bool are_po_ordered(unsigned a, unsigned b)
  {
    if(operator[](a).thread!=operator[](b).thread)
      return false;

    for(std::list<unsigned>::iterator it=po_order.begin();
      it!=po_order.end();it++)
      if(*it==a)
        return true;
      else if(*it==b)
        return false;

    return false;
  }

  void clear()
  {
    po_graph.clear();
    com_graph.clear();
    map_data_dp.clear();
  }

  /* Tarjan 1972 adapted and modified for events + po-transitivity */
  void collect_cycles(std::set<critical_cyclet>& set_of_cycles, 
    weak_memory_modelt model,
    const std::set<unsigned>& filter)
  {
    graph_conc_explorert exploration(*this, max_var, max_po_trans,filter);
    exploration.collect_cycles(set_of_cycles,model);
  }

  void collect_cycles(std::set<critical_cyclet>& set_of_cycles,
    weak_memory_modelt model)
  {
    graph_explorert exploration(*this, max_var, max_po_trans);
    exploration.collect_cycles(set_of_cycles,model);
  }

  void set_parameters_collection(unsigned _max_var = 0, 
    unsigned _max_po_trans = 0)
  {
    max_var = _max_var;
    max_po_trans = _max_po_trans;
  }
};


void test();

#endif
