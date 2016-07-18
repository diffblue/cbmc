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
#include <ostream>
#include <cassert>
#include <algorithm>

class empty_edget
{
};

template<class E=empty_edget>
class graph_nodet
{
public:
  typedef std::size_t node_indext;

  typedef E edget;
  typedef std::map<node_indext, edget> edgest;

  edgest in, out;
  
  inline void add_in(node_indext n)
  {
    in.insert(std::pair<node_indext, edget>(n, edget()));
  }
  
  inline void add_out(node_indext n)
  {
    out.insert(std::pair<node_indext, edget>(n, edget()));
  }

  inline void erase_in(node_indext n)
  {
    in.erase(n);
  }
  
  inline void erase_out(node_indext n)
  {
    out.erase(n);
  }
};

// a node type with an extra bit
template<class E>
class visited_nodet:public graph_nodet<E>
{
public:
  typedef typename graph_nodet<E>::edget edget;
  typedef typename graph_nodet<E>::edgest edgest;

  bool visited;

  inline visited_nodet():visited(false)
  {
  }
};

// compute intersection of two edge sets,
// in linear time
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

// a generic graph class with a parametric node type  
template<class N=graph_nodet<empty_edget> >
class graph
{
public:
  typedef N nodet;
  typedef typename nodet::edgest edgest;
  typedef std::vector<nodet> nodest;
  typedef typename nodet::edget edget;
  typedef typename nodet::node_indext node_indext;

protected:
  nodest nodes;
  
public:
  inline node_indext add_node()
  {
    node_indext no=nodes.size();
    nodes.push_back(nodet());
    return no;
  }
  
  inline node_indext add_node(const nodet& node)
  {
    node_indext no=nodes.size();
    nodes.push_back(node);
    return no;
  }
  
  inline void swap(graph &other)
  {
    nodes.swap(other.nodes);
  }

  inline bool has_edge(node_indext i, node_indext j) const
  {
    return nodes[i].out.find(j)!=nodes[i].out.end();
  }

  inline const nodet &operator[](node_indext n) const
  {
    return nodes[n];
  }

  inline nodet &operator[](node_indext n)
  {
    return nodes[n];
  }
  
  inline void resize(node_indext s)
  {
    nodes.resize(s);
  }
  
  inline std::size_t size() const
  {
    return nodes.size();
  }
  
  inline const edgest &in(node_indext n) const
  {
    return nodes[n].in;
  }

  inline const edgest &out(node_indext n) const
  {
    return nodes[n].out;
  }
  
  inline void add_edge(node_indext a, node_indext b)
  {
    nodes[a].add_out(b);
    nodes[b].add_in(a);
  }
  
  inline void remove_edge(node_indext a, node_indext b)
  {
    nodes[a].erase_out(b);
    nodes[b].erase_in(a);
  }
  
  inline edget &edge(node_indext a, node_indext b)
  {
    return nodes[a].out[b];
  }
  inline const edget &edge(node_indext a, node_indext b) const
  {
    return nodes[a].out.at(b);
  }

  void add_undirected_edge(node_indext a, node_indext b);
  void remove_undirected_edge(node_indext a, node_indext b);
  void remove_in_edges(node_indext n);
  void remove_out_edges(node_indext n);
  
  inline void remove_edges(node_indext n)
  {
    remove_in_edges(n);
    remove_out_edges(n);
  }
  
  inline void clear()
  {
    nodes.clear();
  }
  
  typedef std::list<node_indext> patht;
  
  inline void shortest_path(
    node_indext src,
    node_indext dest,
    patht &path) const
  {
    shortest_path(src, dest, path, false);
  }

  inline void shortest_loop(
    node_indext node,
    patht &path) const
  {
    shortest_path(node, node, path, true);
  }
    
  void visit_reachable(node_indext src);
  
  void make_chordal();
  
  // return value: number of connected subgraphs
  std::size_t connected_subgraphs(
    std::vector<node_indext> &subgraph_nr);

  // return value: number of SCCs
  std::size_t SCCs(std::vector<node_indext> &subgraph_nr);
  
  void output_dot(std::ostream &out) const;
  void output_dot_node(std::ostream &out, node_indext n) const;

protected:
  class tarjant
  {
  public:
    std::vector<bool> visited;
    std::vector<unsigned> depth;
    std::vector<unsigned> lowlink;
    std::vector<bool> in_scc;
    std::stack<node_indext> scc_stack;
    std::vector<node_indext> &subgraph_nr;

    std::size_t scc_count, max_dfs;

    tarjant(std::size_t n, std::vector<node_indext> &_subgraph_nr):
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

  void tarjan(class tarjant &t, node_indext v);

  void shortest_path(
    node_indext src,
    node_indext dest,
    patht &path,
    bool non_trivial) const;
};

/*******************************************************************\

Function: graph::add_undirected_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::add_undirected_edge(node_indext a, node_indext b)
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
void graph<N>::remove_undirected_edge(node_indext a, node_indext b)
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
void graph<N>::remove_in_edges(node_indext n)
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
void graph<N>::remove_out_edges(node_indext n)
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
  node_indext src,
  node_indext dest,
  patht &path,
  bool non_trivial) const
{
  std::vector<bool> visited;
  std::vector<unsigned> distance;
  std::vector<unsigned> previous;
  
  // initialization
  visited.resize(nodes.size(), false);
  distance.resize(nodes.size(), (unsigned)(-1));
  previous.resize(nodes.size(), 0);

  if(!non_trivial)
  {
    distance[src]=0;
    visited[src]=true;
  }

  // does BFS, not Dijkstra
  // we hope the graph is sparse
  std::vector<node_indext> frontier_set, new_frontier_set;
  
  frontier_set.reserve(nodes.size());

  frontier_set.push_back(src);
  
  unsigned d=0;
  bool found=false;
  
  while(!frontier_set.empty() && !found)
  {
    d++;
  
    new_frontier_set.clear();
    new_frontier_set.reserve(nodes.size());
  
    for(typename std::vector<node_indext>::const_iterator
        f_it=frontier_set.begin();
        f_it!=frontier_set.end() && !found;
        f_it++)
    {
      node_indext i=*f_it;
      const nodet &n=nodes[i];
      
      // do all neighbors
      for(typename edgest::const_iterator
          o_it=n.out.begin();
          o_it!=n.out.end() && !found;
          o_it++)
      {
        node_indext o=o_it->first;
      
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
    if(distance[dest]==0 ||
       previous[dest]==src) break; // we are there
    assert(dest!=previous[dest]);
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
void graph<N>::visit_reachable(node_indext src)
{
  // DFS

  std::stack<node_indext> s;
  s.push(src);

  while(!s.empty())
  {
    node_indext n=s.top();
    s.pop();

    nodet &node=nodes[n];
    node.visited=true;

    for(typename edgest::const_iterator
        it=node.out.begin();
        it!=node.out.end();
        it++)
      if(!nodes[it->first].visited)
        s.push(it->first);
  }
}

/*******************************************************************\

Function: graph::connected_subgraphs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
std::size_t graph<N>::connected_subgraphs(
  std::vector<node_indext> &subgraph_nr)
{
  std::vector<bool> visited;
  
  visited.resize(nodes.size(), false);
  subgraph_nr.resize(nodes.size(), 0);

  std::size_t nr=0;
  
  for(node_indext src=0; src<size(); src++)
  {
    if(visited[src]) continue;

    // DFS

    std::stack<node_indext> s;
    s.push(src);

    while(!s.empty())
    {
      node_indext n=s.top();
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
void graph<N>::tarjan(tarjant &t, node_indext v)
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
    node_indext vp=it->first;
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
      node_indext vp=t.scc_stack.top();
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
std::size_t graph<N>::SCCs(std::vector<node_indext> &subgraph_nr)
{
  tarjant t(nodes.size(), subgraph_nr);

  for(node_indext v0=0; v0<size(); v0++)
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

  for(node_indext i=0; i<tmp.size(); i++)
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
  for(node_indext n=0; n<nodes.size(); n++)
    output_dot_node(out, n);
}

/*******************************************************************\

Function: graph::output_dot_node

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void graph<N>::output_dot_node(std::ostream &out, node_indext n) const
{
  const nodet &node=nodes[n];

  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++)
    out << n << " -> " << it->first << '\n';
}

#endif
