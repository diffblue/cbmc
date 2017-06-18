/*******************************************************************\

Module: AND-Inverter Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// AND-Inverter Graph

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

  aig_nodet()
  {
  }

  bool is_and() const
  {
    return a.var_no()!=literalt::unused_var_no();
  }

  bool is_var() const
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
  aigt()
  {
  }

  ~aigt()
  {
  }

  using nodet = aig_nodet;
  using nodest = std::vector<nodet>;
  nodest nodes;

  void clear()
  {
    nodes.clear();
  }

  using terminal_sett = std::set<literalt::var_not>;
  typedef std::map<literalt::var_not, terminal_sett> terminalst;

  // produces the support set
  // should get re-written
  void get_terminals(terminalst &terminals) const;

  const aig_nodet &get_node(literalt l) const
  {
    return nodes[l.var_no()];
  }

  aig_nodet &get_node(literalt l)
  {
    return nodes[l.var_no()];
  }

  nodest::size_type number_of_nodes() const
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

  void print(std::ostream &out) const;
  void print(std::ostream &out, literalt a) const;
  void output_dot_node(std::ostream &out, nodest::size_type v) const;
  void output_dot_edge(
    std::ostream &out, nodest::size_type v, literalt l) const;
  void output_dot(std::ostream &out) const;

  std::string label(nodest::size_type v) const;
  std::string dot_label(nodest::size_type v) const;

protected:
  const std::set<literalt::var_not> &get_terminals_rec(
    literalt::var_not n,
    terminalst &terminals) const;
};

std::ostream &operator << (std::ostream &, const aigt &);

class aig_plus_constraintst:public aigt
{
public:
  using constraintst = std::vector<literalt>;
  constraintst constraints;

  void clear()
  {
    aigt::clear();
    constraints.clear();
  }
};

#endif // CPROVER_SOLVERS_PROP_AIG_H
