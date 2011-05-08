/*******************************************************************\

Module: AND-Inverter Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_PROP_AIG_H
#define CPROVER_SOLVERS_PROP_AIG_H

#include <vector>
#include <set>
#include <map>

#include <solvers/prop/prop.h>

class aig_nodet
{
public:
  typedef enum { UNKNOWN, AND, VAR } typet;
  typet type;
  literalt a, b;
  
  aig_nodet():type(UNKNOWN)
  {
    a.clear();
    b.clear();
  }
  
  bool is_and() const
  {
    return type==AND;
  }
  
  bool is_var() const
  {
    return type==VAR;
  }
  
  void make_and(literalt _a, literalt _b)
  {
    type=AND;
    a=_a;
    b=_b;
  }
  
  void make_var()
  {
    type=VAR;
  }
};

class aigt
{
public:
  aigt()
  {
  }
  
  virtual ~aigt()
  {
  }
  
  void clear()
  {
    nodes.clear();
  }
  
  typedef std::set<unsigned> terminal_sett;
  typedef std::map<unsigned, terminal_sett> terminalst;

  void get_terminals(terminalst &terminals) const;

  const aig_nodet &get_node(literalt l) const
  {
    return nodes[l.var_no()];
  }
  
  const aig_nodet &get_node(unsigned v) const
  {
    return nodes[v];
  }
  
  aig_nodet &get_node(literalt l)
  {
    return nodes[l.var_no()];
  }
  
  aig_nodet &get_node(unsigned v)
  {
    return nodes[v];
  }
  
  unsigned number_of_nodes() const
  {
    return nodes.size();
  }
  
  void swap(aigt &g)
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
  
  literalt new_var_node()
  {
    literalt l=new_node();
    nodes.back().make_var();
    return l;
  }
  
  literalt new_and_node(literalt a, literalt b)
  {
    literalt l=new_node();
    nodes.back().make_and(a, b);
    return l;
  }
  
  bool empty() const
  {
    return nodes.empty();
  }
  
  typedef std::vector<aig_nodet> nodest;
  nodest nodes;

  virtual void print(std::ostream &out) const;
  virtual void print(std::ostream &out, literalt a) const;
  virtual void output_dot_node(std::ostream &out, unsigned v) const;
  virtual void output_dot_edge(std::ostream &out, unsigned v, literalt l) const;
  virtual void output_dot(std::ostream &out) const;

  virtual std::string label(unsigned v) const;
  virtual std::string dot_label(unsigned v) const;

protected:  
  const std::set<unsigned> &get_terminals_rec(
    unsigned n,
    terminalst &terminals) const;
};

std::ostream &operator << (std::ostream &, const aigt &);

#endif
