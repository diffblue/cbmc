/*******************************************************************\

Module: ILP construction for all cycles and resolution

Author: Vincent Nimal

\*******************************************************************/

#ifndef CPROVER_FENCE_INSERTER_H
#define CPROVER_FENCE_INSERTER_H

#include <goto-instrument/wmm/event_graph.h>
#include <goto-instrument/wmm/wmm.h>

// Note: no forward declaration for instrumentert as we derive fence_insertert
#include <goto-instrument/wmm/goto2graph.h>

#include <set>
#include <map>

#include "graph_visitor.h"
#include "cycles_visitor.h"

class abstract_eventt;
class ilpt;

// TODO: can be indirectly replaced by a list without redundancy
// (not a set though)
struct mip_vart
{ 
  typedef event_grapht::critical_cyclet::delayt edget;

  unsigned unique;

  std::map<unsigned, edget> map_to_e;
  std::map<edget, unsigned> map_from_e;

  unsigned add_edge(const edget &e)
  {
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

  mip_vart():unique(0)
  {
  }
};

/* in essence: cycles + goto-prog -> ilp */
class fence_insertert
{
public:
  typedef event_grapht::critical_cyclet::delayt edget;

  instrumentert &instrumenter;

  /* normal variables used almost everytime */
  std::map<unsigned, edget>& map_to_e;
  std::map<edget, unsigned>& map_from_e;
  inline unsigned add_edge(const edget& e) { return var.add_edge(e); }
  inline unsigned add_invisible_edge(const edget& e) {
    return invisible_var.add_edge(e);}

  /* number of contraints */
  unsigned constraints_number;
  const memory_modelt model;

  /* to retrieve the concrete graph edges involved in the (abstract) cycles */
  const_graph_visitort const_graph_visitor;

protected:
  unsigned& unique;
  unsigned fence_options;

  /* MIP variables to edges in po^+/\C */
  mip_vart var;

  /* MIP invisible variables (com) */
  mip_vart invisible_var;

  /* MIP matrix construction */
  void mip_set_var(ilpt& ilp, unsigned& i);
  void mip_set_cst(ilpt& ilp, unsigned& i);
  void mip_fill_matrix(ilpt& ilp, unsigned& i, unsigned const_constraints_number,
    unsigned const_unique);

  /* preprocessing (necessary as glpk static) and solving */
  void preprocess();
  void solve();

  typedef enum {Fence=0, Dp=1, Lwfence=2, Branching=3, Ctlfence=4} fence_typet;
  virtual unsigned fence_cost(fence_typet e) const;

  std::string to_string(fence_typet f) const;

  /* for the preprocessing */
  std::set<unsigned> po;
  std::list<std::set<unsigned> > powr_constraints;
  std::list<std::set<unsigned> > poww_constraints;
  std::list<std::set<unsigned> > porw_constraints;
  std::list<std::set<unsigned> > porr_constraints;
  std::list<std::set<unsigned> > com_constraints;

  /* to retrieve the edges involved in the cycles */
  cycles_visitort cycles_visitor;

  /* conversion column <-> (MIP variable, fence type) */
  unsigned col_to_var(unsigned u) const;
  fence_typet col_to_fence(unsigned u) const;
  unsigned var_fence_to_col(fence_typet f, unsigned var) const;

  /* for the frequencies sum */
  const float epsilon;
  const bool with_freq;
  std::map<unsigned, float> freq_table;

  void import_freq();

  /* computes the fence options */
  void compute_fence_options();
 
  /* debug */
  void print_vars() const;

  /* storing final results */
  std::map<edget, fence_typet> fenced_edges;

public:
  explicit fence_insertert(instrumentert &instr):
    instrumenter(instr), map_to_e(var.map_to_e), map_from_e(var.map_from_e), 
    constraints_number(0), model(TSO),  const_graph_visitor(*this), 
    unique(var.unique), fence_options(0), cycles_visitor(*this), 
    epsilon(0.001), with_freq(false)
  {
  }

  fence_insertert(instrumentert &instr, memory_modelt _model):
    instrumenter(instr), map_to_e(var.map_to_e), map_from_e(var.map_from_e),
    constraints_number(0), model(_model),  const_graph_visitor(*this),
    unique(var.unique), fence_options(0), cycles_visitor(*this), 
    epsilon(0.001), with_freq(false)
  {
  }

  /* do it */
  void compute(); 

  /* selection methods */
  // Note: process_selection updates the selection of cycles in instrumenter,
  // whereas filter just ignores some
  virtual void process_cycles_selection() { }
  virtual bool filter_cycles(unsigned cycle_id) const { return false; }

  /* prints final results */
  void print_to_file();
  void print_to_file_2();
  void print_to_file_3();
  void print_to_file_4();
  
  /* TODO: to be replaced eventually by ns.lookup and basename */
  static std::string remove_extra(const irep_idt& id)
  {
     const std::string copy=id2string(id);
     return remove_extra(copy);
  }

  static std::string remove_extra(std::string copy)
  {
     if(copy.find("::")==std::string::npos)
       return copy;
     return copy.substr(copy.find_last_of("::")+1);
  }

  typet get_type(const irep_idt &id);
  typet type_component(
    std::list<std::string>::const_iterator it, 
    std::list<std::string>::const_iterator end,
    const typet &type);
};

#endif
