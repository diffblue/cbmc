/*******************************************************************\

Module: A Template Class for Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A Template Class for Graphs

#ifndef CPROVER_UTIL_GRAPH_H
#define CPROVER_UTIL_GRAPH_H

#include <list>
#include <stack>
#include <map>
#include <vector>
#include <ostream>
#include <cassert>
#include <algorithm>
#include <queue>

#include "invariant.h"

class empty_edget
{
};

/// This class represents a node in a directed graph.
/// See \ref grapht for more information.
template<class E=empty_edget>
class graph_nodet
{
public:
  typedef std::size_t node_indext;

  typedef E edget;
  typedef std::map<node_indext, edget> edgest;

  edgest in, out;

  void add_in(node_indext n)
  {
    in.insert(std::pair<node_indext, edget>(n, edget()));
  }

  void add_out(node_indext n)
  {
    out.insert(std::pair<node_indext, edget>(n, edget()));
  }

  void erase_in(node_indext n)
  {
    in.erase(n);
  }

  void erase_out(node_indext n)
  {
    out.erase(n);
  }
};

/// A node type with an extra bit
template<class E>
class visited_nodet:public graph_nodet<E>
{
public:
  typedef typename graph_nodet<E>::edget edget;
  typedef typename graph_nodet<E>::edgest edgest;

  bool visited;

  visited_nodet():visited(false)
  {
  }
};

/// Compute intersection of two edge sets, in linear time
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

/// A generic directed graph with a parametric node type.
///
/// The nodes of the graph are stored in the only field of the class, a
/// std::vector named `nodes`. Nodes are instances of class graph_nodet<E> or a
/// subclass of it. Graph edges contain a payload object of parametric type E
/// (which has to be default-constructible).  By default E is instantiated with
/// an empty class (empty_edget).
///
/// Each node is identified by its offset inside the `nodes` vector. The
/// incoming and outgoing edges of a node are stored as std::maps in the fields
/// `in` and `out` of the graph_nodet<E>. These maps associate a node identifier
/// (the offset) to the edge payload (of type E).
///
/// In fact, observe that two instances of E are stored per edge of the graph.
/// For instance, assume that we want to create a graph with two nodes, A and B,
/// and one edge from A to B, labelled by object e. We achieve this by inserting
/// the pair (offsetof(B),e) in the map `A.out` and the pair (offsetof(A),e) in
/// the map `B.in`.
///
/// Nodes are inserted in the graph using grapht::add_node(), which returns the
/// identifier (offset) of the inserted node. Edges between nodes are created
/// by grapht::add_edge(a,b), where `a` and `b` are the identifiers of nodes.
/// Method `add_edges` adds a default-constructed payload object of type E.
/// Adding a payload objet `e` to an edge seems to be only possibly by manually
/// inserting `e` in the std::maps `in` and `out` of the two nodes associated to
/// the edge.
template<class N=graph_nodet<empty_edget> >
class grapht
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
  node_indext add_node()
  {
    node_indext no=nodes.size();
    nodes.push_back(nodet());
    return no;
  }

  void swap(grapht &other)
  {
    nodes.swap(other.nodes);
  }

  bool has_edge(node_indext i, node_indext j) const
  {
    return nodes[i].out.find(j)!=nodes[i].out.end();
  }

  const nodet &operator[](node_indext n) const
  {
    return nodes[n];
  }

  nodet &operator[](node_indext n)
  {
    return nodes[n];
  }

  void resize(node_indext s)
  {
    nodes.resize(s);
  }

  std::size_t size() const
  {
    return nodes.size();
  }

  bool empty() const
  {
    return nodes.empty();
  }

  const edgest &in(node_indext n) const
  {
    return nodes[n].in;
  }

  const edgest &out(node_indext n) const
  {
    return nodes[n].out;
  }

  void add_edge(node_indext a, node_indext b)
  {
    nodes[a].add_out(b);
    nodes[b].add_in(a);
  }

  void remove_edge(node_indext a, node_indext b)
  {
    nodes[a].erase_out(b);
    nodes[b].erase_in(a);
  }

  edget &edge(node_indext a, node_indext b)
  {
    return nodes[a].out[b];
  }

  void add_undirected_edge(node_indext a, node_indext b);
  void remove_undirected_edge(node_indext a, node_indext b);
  void remove_in_edges(node_indext n);
  void remove_out_edges(node_indext n);

  void remove_edges(node_indext n)
  {
    remove_in_edges(n);
    remove_out_edges(n);
  }

  void clear()
  {
    nodes.clear();
  }

  typedef std::list<node_indext> patht;

  void shortest_path(
    node_indext src,
    node_indext dest,
    patht &path) const
  {
    shortest_path(src, dest, path, false);
  }

  void shortest_loop(
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

  bool is_dag() const
  {
    return empty() || !topsort().empty();
  }

  std::list<node_indext> topsort() const;

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

template<class N>
void grapht<N>::add_undirected_edge(node_indext a, node_indext b)
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

template<class N>
void grapht<N>::remove_undirected_edge(node_indext a, node_indext b)
{
  nodet &na=nodes[a];
  nodet &nb=nodes[b];
  na.out.erase(b);
  nb.out.erase(a);
  na.in.erase(b);
  nb.in.erase(a);
}

template<class N>
void grapht<N>::remove_in_edges(node_indext n)
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

template<class N>
void grapht<N>::remove_out_edges(node_indext n)
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

template<class N>
void grapht<N>::shortest_path(
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

template<class N>
void grapht<N>::visit_reachable(node_indext src)
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

template<class N>
std::size_t grapht<N>::connected_subgraphs(
  std::vector<node_indext> &subgraph_nr)
{
  std::vector<bool> visited;

  visited.resize(nodes.size(), false);
  subgraph_nr.resize(nodes.size(), 0);

  std::size_t nr=0;

  for(node_indext src=0; src<size(); src++)
  {
    if(visited[src])
      continue;

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

template<class N>
void grapht<N>::tarjan(tarjant &t, node_indext v)
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
      if(vp==v)
        break;
    }

    t.scc_count++;
  }
}

template<class N>
std::size_t grapht<N>::SCCs(std::vector<node_indext> &subgraph_nr)
{
  tarjant t(nodes.size(), subgraph_nr);

  for(node_indext v0=0; v0<size(); v0++)
    if(!t.visited[v0])
      tarjan(t, v0);

  return t.scc_count;
}

template<class N>
void grapht<N>::make_chordal()
{
  grapht tmp(*this);

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

/// Find a topological order of the nodes if graph is DAG, return empty list for
/// non-DAG or empty graph. Uses Kahn's algorithm running in O(n_edges+n_nodes).
template<class N>
std::list<typename grapht<N>::node_indext> grapht<N>::topsort() const
{
  // list of topologically sorted nodes
  std::list<node_indext> nodelist;
  // queue of working set nodes with in-degree zero
  std::queue<node_indext> indeg0_nodes;
  // in-degree for each node
  std::vector<size_t> in_deg(nodes.size(), 0);

  // abstract graph as in-degree of each node
  for(node_indext idx=0; idx<nodes.size(); idx++)
  {
    in_deg[idx]=in(idx).size();
    if(in_deg[idx]==0)
      indeg0_nodes.push(idx);
  }

  while(!indeg0_nodes.empty())
  {
    node_indext source=indeg0_nodes.front();
    indeg0_nodes.pop();
    nodelist.push_back(source);

    for(const auto &edge : out(source))
    {
      const node_indext target=edge.first;
      INVARIANT(in_deg[target]!=0, "in-degree of node cannot be zero here");

      // remove edge from graph, by decrementing the in-degree of target
      // outgoing edges from source will not be traversed again
      in_deg[target]--;
      if(in_deg[target]==0)
        indeg0_nodes.push(target);
    }
  }

  // if all nodes are sorted, the graph is acyclic
  // return empty list in case of cyclic graph
  if(nodelist.size()!=nodes.size())
    nodelist.clear();
  return nodelist;
}

template<class N>
void grapht<N>::output_dot(std::ostream &out) const
{
  for(node_indext n=0; n<nodes.size(); n++)
    output_dot_node(out, n);
}

template<class N>
void grapht<N>::output_dot_node(std::ostream &out, node_indext n) const
{
  const nodet &node=nodes[n];

  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++)
    out << n << " -> " << it->first << '\n';
}

#endif // CPROVER_UTIL_GRAPH_H
