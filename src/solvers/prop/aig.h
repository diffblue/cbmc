/*******************************************************************\

Module: AND-Inverter Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_PROP_AIG_H
#define CPROVER_SOLVERS_PROP_AIG_H

#include <vector>
#include <set>
#include <map>

#include <solvers/prop/literal.h>

class aig_nodet
{
public:
  literalt a, b;
  
  inline aig_nodet()
  {
  }
  
  inline bool is_and() const
  {
    return a.var_no()!=literalt::unused_var_no();
  }
  
  inline bool is_var() const
  {
    return a.var_no()==literalt::unused_var_no();
  }
  
  void make_and(literalt _a, literalt _b)
  {
    a=_a;
    b=_b;
  }
  
  void make_var()
  {
    a.set(literalt::unused_var_no(), false);
  }
};

class aigt
{
public:
  inline aigt()
  {
  }
  
  ~aigt()
  {
  }
  
  typedef aig_nodet nodet;  
  typedef std::vector<nodet> nodest;
  nodest nodes;

  inline void clear()
  {
    nodes.clear();
  }
  
  typedef std::set<unsigned> terminal_sett;
  typedef std::map<unsigned, terminal_sett> terminalst;

  // produces the support set
  // should get re-written
  void get_terminals(terminalst &terminals) const;

  inline const aig_nodet &get_node(literalt l) const
  {
    return nodes[l.var_no()];
  }
  
  inline aig_nodet &get_node(literalt l)
  {
    return nodes[l.var_no()];
  }
  
  inline nodest::size_type number_of_nodes() const
  {
    return nodes.size();
  }
  
  inline void swap(aigt &g)
  {
    nodes.swap(g.nodes);
  }
  
  literalt new_node()
  {
    nodes.push_back(aig_nodet());
    literalt l;
    l.set(nodes.size()-1, false);
    return l;
  }
  
  inline literalt new_var_node()
  {
    literalt l=new_node();
    nodes.back().make_var();
    return l;
  }
  
  inline literalt new_and_node(literalt a, literalt b)
  {
    literalt l=new_node();
    nodes.back().make_and(a, b);
    return l;
  }
  
  inline bool empty() const
  {
    return nodes.empty();
  }

  void print(std::ostream &out) const;
  void print(std::ostream &out, literalt a) const;
  void output_dot_node(std::ostream &out, nodest::size_type v) const;
  void output_dot_edge(std::ostream &out, nodest::size_type v, literalt l) const;
  void output_dot(std::ostream &out) const;

  std::string label(nodest::size_type v) const;
  std::string dot_label(nodest::size_type v) const;

protected:  
  const std::set<unsigned> &get_terminals_rec(
    unsigned n,
    terminalst &terminals) const;
};

std::ostream &operator << (std::ostream &, const aigt &);

#endif
