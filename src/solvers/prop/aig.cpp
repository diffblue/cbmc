/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <ostream>

#include <util/i2string.h>

#include "aig.h"

/*******************************************************************\

Function: aigt::label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string aigt::label(nodest::size_type v) const
{
  return "var("+i2string(v)+")";
}

/*******************************************************************\

Function: aigt::dot_label

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string aigt::dot_label(nodest::size_type v) const
{
  return "var("+i2string(v)+")";
}

/*******************************************************************\

Function: aigt::get_terminals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::get_terminals(terminalst &terminals) const
{
  for(nodest::size_type n=0; n<nodes.size(); n++)
    get_terminals_rec(n, terminals);
}

/*******************************************************************\

Function: aigt::get_terminals_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const aigt::terminal_sett &aigt::get_terminals_rec(
  unsigned n,
  terminalst &terminals) const
{
  terminalst::iterator it=terminals.find(n);
  
  if(it!=terminals.end())
    return it->second; // already done
  
  assert(n<nodes.size());
  const aig_nodet &node=nodes[n];
  
  terminal_sett &t=terminals[n];

  if(node.is_and())
  {
    if(!node.a.is_constant())
    {
      const std::set<unsigned> &ta=get_terminals_rec(node.a.var_no(), terminals);
      t.insert(ta.begin(), ta.end());
    }

    if(!node.b.is_constant())
    {
      const std::set<unsigned> &tb=get_terminals_rec(node.b.var_no(), terminals);
      t.insert(tb.begin(), tb.end());
    }
  }
  else // this is a terminal
  {
    t.insert(n);
  }
    
  return t;
}

/*******************************************************************\

Function: aigt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::print(
  std::ostream& out,
  literalt a) const
{
  if(a==const_literal(false))
  {
    out << "FALSE";
    return;
  }
  else if(a==const_literal(true))
  {
    out << "TRUE";
    return;
  }

  unsigned node_nr=a.var_no();

  {
    const aig_nodet &node=nodes[node_nr];

    if(node.is_and())
    {
      if(a.sign()) out << "!(";
      print(out, node.a);
      out << " & ";
      print(out, node.b);
      if(a.sign()) out << ")";
    }
    else if(node.is_var())
    {
      if(a.sign()) out << "!";
      out << label(node_nr);\
    }
    else
    {
      if(a.sign()) out << "!";
      out << "unknown(" << node_nr << ")";
    }
  }
}

/*******************************************************************\

Function: aigt::output_dot_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::output_dot_node(
  std::ostream &out,
  nodest::size_type v) const
{
  const aig_nodet &node=nodes[v];

  if(node.is_and())
  {
    out << v << " [label=\"" << v << "\"]" << "\n";
    output_dot_edge(out, v, node.a);
    output_dot_edge(out, v, node.b);
  }
  else // the node is a terminal
  {
    out << v << " [label=\"" << dot_label(v) << "\""
        << ",shape=box]" << "\n";
  }
}

/*******************************************************************\

Function: aigt::output_dot_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::output_dot_edge(
  std::ostream& out,
  nodest::size_type v,
  literalt l) const
{
  if(l.is_true())
  {
    out << "TRUE -> " << v;
  }
  else if(l.is_false())
  {
    out << "TRUE -> " << v;
    out << " [arrowhead=odiamond]";
  }
  else
  {
    out << l.var_no() << " -> " << v;
    if(l.sign()) out << " [arrowhead=odiamond]";
  }

  out << "\n";
}

/*******************************************************************\

Function: aigt::output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::output_dot(std::ostream& out) const
{
  // constant TRUE
  out << "TRUE [label=\"TRUE\", shape=box]" << "\n";

  // now the nodes
  for(nodest::size_type n=0; n<number_of_nodes(); n++)
    output_dot_node(out, n);
}

/*******************************************************************\

Function: aigt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void aigt::print(std::ostream &out) const
{
  for(nodest::size_type n=0; n<number_of_nodes(); n++)
  {
    out << "n" << n << " = ";
    literalt l;
    l.set(n, false);
    print(out, l);
    out << "\n";
  }
}

/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (std::ostream &out, const aigt &aig)
{
  aig.print(out);
  return out;
}
