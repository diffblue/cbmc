/*******************************************************************\

Module: ILP construction for all cycles and resolution

Author: Vincent Nimal

\*******************************************************************/

#ifndef CPROVER_FENCE_INSERTER_H
#define CPROVER_FENCE_INSERTER_H

#include <goto-instrument/wmm/event_graph.h>
#include <goto-instrument/wmm/wmm.h>
#include <util/message.h>

// Note: no forward declaration for instrumentert as we derive fence_insertert
#include <goto-instrument/wmm/goto2graph.h>

#include <set>
#include <map>
#include <sstream>
#include <fstream>

#ifdef HAVE_GLPK
#include <glpk.h>
#endif

class abstract_eventt;

class fence_insertert
{
protected:
  typedef event_grapht::critical_cyclet::delayt edget;

  // TODO: can be indirectly replaced by a list without redundancy
  // (not a set though)
  struct mip_vart 
  {
    unsigned unique;

    std::map<unsigned, edget> map_to_e;
    std::map<edget, unsigned> map_from_e;

    unsigned add_edge(const edget& e) {
      if(map_from_e.find(e) != map_from_e.end())
        return map_from_e[e];
      else
      {
        ++unique;
        map_to_e.insert(std::pair<unsigned, edget>(unique, e));
        map_from_e[e] = unique;
        return unique;
      }
    }

    mip_vart():unique(0){}
  };

  instrumentert &instrumenter;
  const memory_modelt model;
  unsigned fence_options;

  /* MIP variables to edges in po^+/\C */
  mip_vart var;

  /* MIP invisible variables (com) */
  mip_vart invisible_var;

  /* normal variables used almost everytime */
  std::map<unsigned, edget>& map_to_e;
  std::map<edget, unsigned>& map_from_e;
  unsigned& unique;
  inline unsigned add_edge(const edget& e) { return var.add_edge(e); }
  inline unsigned add_invisible_edge(const edget& e) { 
    return invisible_var.add_edge(e);}

  /* computes the PT (btwn), CT (cml) and IT (cntrl) */
  void PT(const edget& e, std::set<unsigned>& edges);
  void CT(const edget& e, std::set<unsigned>& edges);
  void CT_not_powr(const edget& e, std::set<unsigned>& edges);
  void IT(const edget& e, std::set<unsigned>& edges);

  /* preprocessing (necessary as glpk static) and solving */
  void preprocess();
  void solve();

  /* MIP matrix construction */
  void mip_set_var(glp_prob* lp, unsigned& i);
  void mip_set_cst(glp_prob* lp, unsigned& i);
  void mip_fill_matrix(glp_prob* lp, unsigned& i, int* imat, int* jmat, 
    double* vmat, const unsigned const_constraints_number, 
    const unsigned const_unique);

  typedef enum {Fence=0, Dp=1, Lwfence=2, Branching=3, Ctlfence=4} fence_typet;
  virtual unsigned fence_cost(fence_typet e) const;

  std::string to_string(fence_typet f) {
    switch(f) {
      case Fence: return "fence";
      case Lwfence: return "lwfence";
      case Dp: return "dp";
      case Branching: return "branching";
      case Ctlfence: return "ctlfence";
    }
    assert (0);
  }

  /* selection methods */
  virtual inline void process_cycles_selection() {}
  virtual inline bool filter_cycles(unsigned cycle_id) const {
    return false; }

  /* computes po^+ edges in U{C_1, ..., C_j} */
  void po_edges(std::set<unsigned>& edges);

  /* computes pairs that will be protected for the 
     TSO/PSO/RMO/Power/ARM by the constraints */
  void powr_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void poww_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void porw_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void porr_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);
  void com_constraint(const event_grapht::critical_cyclet& C_j,
    std::set<unsigned>& edges);

  /* for the preprocessing */
  std::set<unsigned> po;
  std::list<std::set<unsigned> > powr_constraints;
  std::list<std::set<unsigned> > poww_constraints;
  std::list<std::set<unsigned> > porw_constraints;
  std::list<std::set<unsigned> > porr_constraints;
  std::list<std::set<unsigned> > com_constraints;
  unsigned constraints_number;

  /* conversion column <-> (MIP variable, fence type) */
  inline unsigned col_to_var(unsigned u) const
  {
    return (u-u%fence_options)/fence_options+(u%fence_options!=0?1:0);
  }

  inline fence_typet col_to_fence(unsigned u) const
  {
    switch(u%fence_options) {
      case 0: return Fence;
      case 1: return Dp;
      case 2: return Lwfence;
      case 3: return Branching;
      case 4: return Ctlfence;
    }
    assert(0);
  }

  inline unsigned var_fence_to_col(fence_typet f, unsigned var)
  {
    switch(f) {
      case Fence: return var*fence_options;
      case Dp: return (var-1)*fence_options+1;
      case Lwfence: return (var-1)*fence_options+2;
      case Branching: return (var-1)*fence_options+3;
      case Ctlfence: return (var-1)*fence_options+4;
    }
    assert(0);
  }

  /* computes the fence options */
  void compute_fence_options()
  {
    switch(model) {
      case TSO:
      case PSO:
      case RMO:
        fence_options = 1; // 2: f, br
        break;
      case Power:
        fence_options = 3; // 5: f, lwf, dp, cf, br
        break;
      case Unknown: /* including ARM */
        fence_options = 2; // 4: f, dp, cf, br
        break;
    }
  }

  std::set<unsigned> visited_nodes;

  void const_graph_explore(event_grapht& graph, unsigned next, unsigned end,
    std::list<unsigned>& old_path);
  void graph_explore(event_grapht& graph, unsigned next, unsigned end, 
    std::list<unsigned>& old_path, std::set<unsigned>& edges);
  void graph_explore_BC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw);
  void graph_explore_AC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path, std::set<unsigned>& edges, bool porw);
  void graph_explore_BC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path, std::set<unsigned>& edges) {
    graph_explore_BC(egraph, next, old_path, edges, false);
  }
  void graph_explore_AC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path, std::set<unsigned>& edges) {
    graph_explore_AC(egraph, next, old_path, edges, false);
  }
  void const_graph_explore_BC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path);
  void const_graph_explore_AC(event_grapht& egraph, unsigned next,
    std::list<unsigned>& old_path);

  /* debug */
  void print_vars() const {
    instrumenter.message.statistics() 
      << "---- pos/pos+ (visible) variables ----" << messaget::eom;
    for(std::map<edget,unsigned>::const_iterator it=map_from_e.begin();
      it!=map_from_e.end(); ++it)
      instrumenter.message.statistics() << it->first.first << "," 
        << it->first.second << messaget::eom;
    instrumenter.message.statistics() << "---- cmp (invisible) variables ----"
      << messaget::eom;
    for(std::map<edget,unsigned>::const_iterator it=
      invisible_var.map_from_e.begin();
      it!=invisible_var.map_from_e.end(); ++it)
      instrumenter.message.statistics() << it->first.first << "," 
        << it->first.second << messaget::eom;
    instrumenter.message.statistics() << "-----------------------------------"
      << messaget::eom;
  }

  /* for the frequencies sum */
  const float epsilon;
  const bool with_freq;
  std::map<unsigned, float> freq_table;

  void import_freq();

  /* storing final results */
  std::map<edget,fence_typet> fenced_edges;

public:
  fence_insertert(instrumentert &instr)
    :instrumenter(instr), model(TSO), fence_options(0), 
      map_to_e(var.map_to_e), map_from_e(var.map_from_e), unique(var.unique),
      constraints_number(0), epsilon(0.001), with_freq(false)
  {}

  fence_insertert(instrumentert &instr, memory_modelt _model)
    :instrumenter(instr), model(_model), fence_options(0), 
      map_to_e(var.map_to_e), map_from_e(var.map_from_e), unique(var.unique),
      constraints_number(0), epsilon(0.001), with_freq(false)
  {}

  /* do it */
  void compute(); 

  /* prints final results */
  void print_to_file()
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];

      s << to_string(it->second) << "|" << first.source_location.get_file() 
        << "|" << first.source_location.get_line() << "|" 
        << first.source_location.get_column() << std::endl;
      non_redundant_display.insert(s.str());
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

  /* prints final results */
  void print_to_file_2() 
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      s << to_string(it->second) << "|" << first.source_location.get_file() 
      << "|" << first.source_location.get_line() << "|" 
      << second.source_location.get_file()
      << "|" << second.source_location.get_line() << std::endl;
      non_redundant_display.insert(s.str());
    }
    
    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

/* prints final results */
  void print_to_file_3()
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      try {
      s << to_string(it->second) << "|" << first.source_location.get_file() 
        << "|" << first.source_location.get_function() << "|" 
        << first.source_location.get_line() << "|" << first.variable << "|"
        << second.source_location.get_file() << "|"
        << second.source_location.get_function() << "|" 
        << second.source_location.get_line()
        << "|" << second.variable << std::endl;
      non_redundant_display.insert(s.str());
      }
      catch (std::string s) {
        instrumenter.message.warning() 
          << "Couldn't retrieve symbols of variables " << first.variable
          << " and " << second.variable << " due to " << s << messaget::eom;
      }
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

  /* prints final results */
  void print_to_file_4()
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      try {
      s << to_string(it->second) << "|" << first.source_location.get_file() 
        << "|" << first.source_location.get_function() << "|" 
        << first.source_location.get_line() 
        << "|" << first.variable << "|" 
        << get_type(first.variable).get("#c_type") << "|"
        << second.source_location.get_file() << "|" 
        << second.source_location.get_function() << "|" 
        << second.source_location.get_line() 
        << "|" << second.variable << "|"
        << get_type(second.variable).get("#c_type") << std::endl;
      non_redundant_display.insert(s.str());
      }
      catch (std::string s) {
        instrumenter.message.warning() 
          << "Couldn't retrieve types of variables " << first.variable
          << " and " << second.variable << " due to " << s << messaget::eom;
      }
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

  /* TODO: to be replaced eventually by ns.lookup and basename */
  static std::string remove_extra(const irep_idt& id) {
     const std::string copy=id2string(id);
     return remove_extra(copy);
  }

  static std::string remove_extra(std::string copy) {
     if(copy.find("::")==std::string::npos)
       return copy;
     return copy.substr(copy.find_last_of("::")+1);
  }

  typet get_type(const irep_idt& id) {
    std::string copy=id2string(id);
    /* if we picked an array, removes [] that rw_set added */
    if(copy.find("[]")!=std::string::npos)
      copy=copy.substr(0, copy.find_last_of("[]")-1);
    try {
      return instrumenter.ns.lookup(copy).type;
    }
    catch (...) {
      std::list<std::string> fields;
      std::string current;
      
      /* collects the consecutive fields */
      std::string::const_iterator it=copy.begin();
      std::string::const_iterator next=it;
      for(; it!=copy.end(); ++it)
      {
        next=it;
        ++next;
        if(! (*it=='.' || (next!=copy.end() && *it=='-' && *next=='>')) ) {
          current+=*it;
          instrumenter.message.debug() << current << messaget::eom;
        }
        else {
          fields.push_back(current);
          current.clear();
          if(*it!='.')
            ++it;
          /* safe as next!=copy.end() */
          assert(next!=copy.end());
        }
      }

      /* retrieves the type of the accessed field */
      typet field=type_component(fields.begin(), fields.end(), 
        instrumenter.ns.lookup(fields.front()).type);
      return field;
    }
  }

  typet type_component(std::list<std::string>::const_iterator it, 
    std::list<std::string>::const_iterator end, const typet& type)
  {
    if(it==end)
      return type;
    
    if(type.id()==ID_struct) {
      const struct_union_typet& str=to_struct_union_type(type);
      typet comp_type=str.component_type(*it);
      ++it;
      return type_component(it, end, comp_type);
    }

    if(type.id()==ID_symbol) {
      return type;
    }

    assert(0);
  }
};

#endif
