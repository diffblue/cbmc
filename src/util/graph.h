/*******************************************************************\

Module: A Template Class for Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef __GRAPH_H
#define __GRAPH_H

#include <list>
#include <stack>
#include <map>
#include <vector>
#include <iostream>
#include <cassert>

class empty_nodet
{
};

template<class E=empty_nodet>
class graph_nodet
{
public:
  typedef E edget;
  typedef std::map<unsigned, edget> edgest;

  edgest in, out;
  
  void add_in(unsigned n)
  {
    in.insert(std::pair<unsigned, edget>(n, edget()));
  }
  
  void add_out(unsigned n)
  {
    out.insert(std::pair<unsigned, edget>(n, edget()));
  }

  void erase_in(unsigned n)
  {
    in.erase(n);
  }
  
  void erase_out(unsigned n)
  {
    out.erase(n);
  }
};

template<class E>
void intersection(
  const typename graph_nodet<E>::edgest &a,
  const typename graph_nodet<E>::edgest &b,
  typename graph_nodet<E>::edgest &dest)
{
  typename graph_nodet<E>::edgest::const_iterator
    it_a=a.begin(), 
    it_b=b.begin();

  while(it_a!=a.end() && it_b!=b.end())
  {
    if(*it_a==*it_b)
    {
      dest.insert(*it_a);
      it_a++;
      it_b++;
    }
    else if(*it_a<*it_b)
      it_a++;
    else // *it_a>*it_b
      it_b++;
  }
}
  
template<class N>
class graph
{
public:
  typedef N nodet;
  typedef typename nodet::edgest edgest;
  typedef std::vector<nodet> nodest;
  typedef typename nodet::edget edget;  

protected:
  nodest nodes;
  
public:
  unsigned add_node()
  {
    unsigned no=nodes.size();
    nodes.push_back(nodet());
    return no;
  }
  
  void swap(graph &other)
  {
    nodes.swap(other.nodes);
  }

  bool has_edge(unsigned i, unsigned j) const
  {
    return nodes[i].out.find(j)!=nodes[i].out.end();
  }

  inline const nodet &operator[](unsigned n) const
  {
    return nodes[n];
  }

  inline nodet &operator[](unsigned n)
  {
    return nodes[n];
  }
  
  inline void resize(unsigned s)
  {
    nodes.resize(s);
  }
  
  inline unsigned size() const
  {
    return nodes.size();
  }
  
  inline const edgest &in(unsigned n) const
  {
    return nodes[n].in;
  }

  inline const edgest &out(unsigned n) const
  {
    return nodes[n].out;
  }
  
  void add_edge(unsigned a, unsigned b)
  {
    nodes[a].add_out(b);
    nodes[b].add_in(a);
  }
  
  void remove_edge(unsigned a, unsigned b)
  {
    nodes[a].erase_out(a);
    nodes[b].erase_in(a);
  }
  
  edget &edge(unsigned a, unsigned b)
  {
    return nodes[a].out[b];
  }

  void add_undirected_edge(unsigned a, unsigned b);
  void remove_undirected_edge(unsigned a, unsigned b);
  void remove_in_edges(unsigned n);
  void remove_out_edges(unsigned n);
  
  void remove_edges(unsigned n)
  {
    remove_in_edges(n);
    remove_out_edges(n);
  }
  
  void clear()
  {
    nodes.clear();
  }
  
  typedef std::list<unsigned> patht;
  
  void shortest_path(
    unsigned src,
    unsigned dest,
    patht &path);
    
  void visit_reachable(unsigned src);
  
  void make_chordal();
  
  // return value: number of connected subgraphs
  unsigned connected_subgraphs(
    std::vector<unsigned> &subgraph_nr);

  // return value: number of SCCs
  unsigned SCCs(std::vector<unsigned> &subgraph_nr);
  
  void output_dot(std::ostream &out) const;
  void output_dot_node(std::ostream &out, unsigned n) const;

protected:
  class tarjant
  {
  public:
    std::vector<bool> visited;
    std::vector<unsigned> depth;
    std::vector<unsigned> lowlink;
    std::vector<bool> in_scc;
    std::stack<unsigned> scc_stack;
    std::vector<unsigned> &subgraph_nr;

    unsigned scc_count, max_dfs;

    tarjant(unsigned n, std::vector<unsigned> &_subgraph_nr):
      subgraph_nr(_subgraph_nr)
    {
      visited.resize(n, false);
      depth.resize(n, 0);
      lowlink.resize(n, 0);
      in_scc.resize(n, false);
      max_dfs=scc_count=0;
      subgraph_nr.resize(n, 0);
    }  
  };

  void tarjan(class tarjant &t, unsigned v);
};

/*******************************************************************\

Function: graph::add_undirected_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::add_undirected_edge(unsigned a, unsigned b)
{
  assert(a<nodes.size());
  assert(b<nodes.size());
  nodet &na=nodes[a];
  nodet &nb=nodes[b];
  na.add_out(b);
  nb.add_out(a);
  na.add_in(b);
  nb.add_in(a);
}

/*******************************************************************\

Function: graph::remove_undirected_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
 
template<class N> 
void graph<N>::remove_undirected_edge(unsigned a, unsigned b)
{
  nodet &na=nodes[a];
  nodet &nb=nodes[b];
  na.out.erase(b);
  nb.out.erase(a);
  na.in.erase(b);
  nb.in.erase(a);
}

/*******************************************************************\

Function: graph::remove_in_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::remove_in_edges(unsigned n)
{
  nodet &node=nodes[n];
  
  // delete all incoming edges
  for(typename edgest::const_iterator
      it=node.in.begin();
      it!=node.in.end();
      it++)
    nodes[it->first].erase_out(n);
    
  node.in.clear();
}

/*******************************************************************\

Function: graph::remove_out_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::remove_out_edges(unsigned n)
{
  nodet &node=nodes[n];
  
  // delete all outgoing edges
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++)
    nodes[it->first].erase_in(n);
  
  node.out.clear();
}

/*******************************************************************\

Function: graph::shortest_path

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::shortest_path(
  unsigned src,
  unsigned dest,
  patht &path)
{
  std::vector<bool> visited;
  std::vector<unsigned> distance;
  std::vector<unsigned> previous;
  
  // initialization
  visited.resize(nodes.size(), false);
  distance.resize(nodes.size(), (unsigned)(-1));
  previous.resize(nodes.size(), 0);

  distance[src]=0;
  visited[src]=true;

  // does BFS, not Dijkstra
  // we hope the graph is sparse
  std::vector<unsigned> frontier_set, new_frontier_set;
  
  frontier_set.reserve(nodes.size());

  frontier_set.push_back(src);
  
  unsigned d=0;
  bool found=false;
  
  while(!frontier_set.empty() && !found)
  {
    d++;
  
    new_frontier_set.clear();
    new_frontier_set.reserve(nodes.size());
  
    for(std::vector<unsigned>::const_iterator
        f_it=frontier_set.begin();
        f_it!=frontier_set.end() && !found;
        f_it++)
    {
      unsigned i=*f_it;
      nodet &n=nodes[i];
      
      // do all neighbors
      for(typename edgest::iterator
          o_it=n.out.begin();
          o_it!=n.out.end() && !found;
          o_it++)
      {
        unsigned o=o_it->first;
      
        if(!visited[o])
        {
          distance[o]=d;
          previous[o]=i;
          visited[o]=true;

          if(o==dest)
            found=true;
          else
            new_frontier_set.push_back(o);
        }
      }
    }
    
    frontier_set.swap(new_frontier_set);
  }
  
  // compute path
  // walk towards 0-distance node
  path.clear();
  
  // reachable at all?
  if(distance[dest]==(unsigned)(-1))
    return; // nah

  while(true)
  {
    path.push_front(dest);
    if(distance[dest]==0) break; // we are there
    dest=previous[dest];
  }
}

/*******************************************************************\

Function: graph::visit_reachable

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::visit_reachable(unsigned src)
{
  // DFS

  std::stack<unsigned> s;
  s.push(src);

  while(!s.empty())
  {
    unsigned n=s.top();
    s.pop();

    nodet &node=nodes[n];
    node.visited=true;

    for(typename edgest::const_iterator
        it=node.out.begin();
        it!=node.out.end();
        it++)
      if(!nodes[*it].visited)
        s.push(*it);
  }
}

/*******************************************************************\

Function: graph::connected_subgraphs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
unsigned graph<N>::connected_subgraphs(
  std::vector<unsigned> &subgraph_nr)
{
  std::vector<bool> visited;
  
  visited.resize(nodes.size(), false);
  subgraph_nr.resize(nodes.size(), 0);

  unsigned nr=0;
  
  for(unsigned src=0; src<size(); src++)
  {
    if(visited[src]) continue;

    // DFS

    std::stack<unsigned> s;
    s.push(src);

    while(!s.empty())
    {
      unsigned n=s.top();
      s.pop();
      
      visited[n]=true;
      subgraph_nr[n]=nr;

      const nodet &node=nodes[n];

      for(typename edgest::const_iterator
          it=node.out.begin();
          it!=node.out.end();
          it++)
        if(!visited[*it])
          s.push(*it);
    }

    nr++;
  }

  return nr;
}

/*******************************************************************\

Function: graph::tarjan

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::tarjan(tarjant &t, unsigned v)
{
  t.scc_stack.push(v);
  t.in_scc[v]=true;
  t.depth[v]=t.max_dfs;
  t.lowlink[v]=t.max_dfs;
  t.visited[v]=true;
  t.max_dfs++;

  const nodet &node=nodes[v];
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++)
  {
    unsigned vp=it->first;
    if(!t.visited[vp])
    {
      tarjan(t, vp);
      t.lowlink[v]=std::min(t.lowlink[v], t.lowlink[vp]);
    }       
    else if(t.in_scc[vp])
      t.lowlink[v]=std::min(t.lowlink[v], t.depth[vp]);
  }

  // check if root of SCC
  if(t.lowlink[v]==t.depth[v])
  {
    while(true)
    {
      assert(!t.scc_stack.empty());
      unsigned vp=t.scc_stack.top();
      t.scc_stack.pop();
      t.in_scc[vp]=false;
      t.subgraph_nr[vp]=t.scc_count;
      if(vp==v) break;
    }

    t.scc_count++;
  }
}

/*******************************************************************\

Function: graph::SCCs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
unsigned graph<N>::SCCs(std::vector<unsigned> &subgraph_nr)
{
  tarjant t(nodes.size(), subgraph_nr);

  for(unsigned v0=0; v0<size(); v0++)
    if(!t.visited[v0])
      tarjan(t, v0);

  return t.scc_count;
}

/*******************************************************************\

Function: graph::make_chordal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::make_chordal()
{
  graph tmp(*this);

  // This assumes an undirected graph.
  // 1. remove all nodes in tmp, reconnecting the remaining ones
  // 2. the chordal graph is the old one plus the new edges

  for(unsigned i=0; i<tmp.size(); i++)
  {
    const nodet &n=tmp[i];

    // connect all the nodes in n.out with each other

    for(typename edgest::const_iterator
        it1=n.out.begin();
        it1!=n.out.end();
        it1++)
      for(typename edgest::const_iterator
          it2=n.out.begin();
          it2!=n.out.end();
          it2++)
      {
        if(*it1!=*it2)
        {
          tmp.add_undirected_edge(*it1, *it2);
          this->add_undirected_edge(*it1, *it2);
        }
      }

    // remove node from tmp graph
    tmp.remove_edges(i);
  }
}

/*******************************************************************\

Function: graph::output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::output_dot(std::ostream &out) const
{
  for(unsigned n=0; n<nodes.size(); n++)
    output_dot_node(out, n);
}

/*******************************************************************\

Function: graph::output_dot_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::output_dot_node(std::ostream &out, unsigned n) const
{
  const nodet &node=nodes[n];

  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++)
    out << n << " -> " << it->first << std::endl;
}

#endif
