/*******************************************************************\

Module: A Template Class for Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A Template Class for Graphs

#ifndef CPROVER_UTIL_GRAPH_H
#define CPROVER_UTIL_GRAPH_H

#include <algorithm>
#include <cassert>
#include <functional>
#include <iosfwd>
#include <list>
#include <map>
#include <queue>
#include <sstream>
#include <stack>
#include <vector>

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

private:
  /// \brief Node with attributes suitable for Graphviz DOT format
  ///
  /// Derived types may override this function to produce more informative DOT
  /// diagrams than the default implementation, which displays only the node
  /// index. The return value should be a list of node attributes within square
  /// brackets that can be parsed by `dot`. Here is a sample implementation for
  /// a fictional node type with `is_evil()` and `is_pink()` functions:
  ///
  ///     std::stringstream ss;
  ///     ss << "[shape=\"" << is_evil() ? "box" : "diamond"
  ///        << "\", color=\"" << is_pink() ? "#e91e63" : "#9c27b0"
  ///        << "\", label=\"this is node " << std::to_string(idx)
  ///        << "\"]";
  ///     return ss.str();
  ///
  virtual std::string dot_attributes(const node_indext &) const
  {
    return "";
  }

public:
  std::string pretty(const node_indext &idx) const
  {
    std::stringstream ss;
    ss << std::to_string(idx) << " " << dot_attributes(idx);
    return ss.str();
  }

  virtual ~graph_nodet()
  {
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

  std::vector<node_indext> get_reachable(node_indext src, bool forwards) const;

  std::vector<node_indext>
  get_reachable(const std::vector<node_indext> &src, bool forwards) const;

  void disconnect_unreachable(node_indext src);
  void disconnect_unreachable(const std::vector<node_indext> &src);

  std::vector<typename N::node_indext>
  depth_limited_search(typename N::node_indext src, std::size_t limit) const;

  std::vector<typename N::node_indext> depth_limited_search(
    std::vector<typename N::node_indext> &src,
    std::size_t limit) const;

  void make_chordal();

  // return value: number of connected subgraphs
  std::size_t connected_subgraphs(
    std::vector<node_indext> &subgraph_nr);

  // return value: number of SCCs
  std::size_t SCCs(std::vector<node_indext> &subgraph_nr) const;

  bool is_dag() const
  {
    return empty() || !topsort().empty();
  }

  std::list<node_indext> topsort() const;

  std::vector<node_indext> get_successors(const node_indext &n) const;
  void output_dot(std::ostream &out) const;
  void for_each_successor(
    const node_indext &n,
    std::function<void(const node_indext &)> f) const;

protected:
  std::vector<typename N::node_indext> depth_limited_search(
    std::vector<typename N::node_indext> &src,
    std::size_t limit,
    std::vector<bool> &visited) const;

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

  void tarjan(class tarjant &t, node_indext v) const;

  void shortest_path(
    node_indext src,
    node_indext dest,
    patht &path,
    bool non_trivial) const;
};

template<class N>
void grapht<N>::add_undirected_edge(node_indext a, node_indext b)
{
  PRECONDITION(a < nodes.size());
  PRECONDITION(b < nodes.size());
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
    INVARIANT(
      dest != previous[dest], "loops cannot be part of the shortest path");
    dest=previous[dest];
  }
}

template<class N>
void grapht<N>::visit_reachable(node_indext src)
{
  std::vector<node_indext> reachable = get_reachable(src, true);
  for(const auto index : reachable)
    nodes[index].visited = true;
}

/// Removes any edges between nodes in a graph that are unreachable from
/// a given start node. Used for computing cone of influence,
/// by disconnecting unreachable nodes and then performing backwards
/// reachability.
/// Note nodes are not actually removed from the vector nodes, because
/// this requires renumbering node indices. This copies the way nodes
/// are "removed" in make_chordal.
/// \param src: start node
template <class N>
void grapht<N>::disconnect_unreachable(node_indext src)
{
  const std::vector<node_indext> source_nodes(1, src);
  disconnect_unreachable(source_nodes);
}

/// Removes any edges between nodes in a graph that are unreachable
/// from a vector of start nodes.
/// \param src: vector of indices of start nodes
template <class N>
void grapht<N>::disconnect_unreachable(const std::vector<node_indext> &src)
{
  std::vector<node_indext> reachable = get_reachable(src, true);
  std::sort(reachable.begin(), reachable.end());
  std::size_t reachable_idx = 0;
  for(std::size_t i = 0; i < nodes.size(); i++)
  {
    // Holds since `reachable` contains node indices (i.e., all elements are
    // smaller than `nodes.size()`), `reachable` is sorted, indices from `0` to
    // `nodes.size()-1` are iterated over by variable i in order, and
    // `reachable_idx` is only incremented when `i == reachable[reachable_idx]`
    // holds.
    INVARIANT(
      reachable_idx >= reachable.size() || i <= reachable[reachable_idx],
      "node index i is smaller or equal to the node index at "
      "reachable[reachable_idx], when reachable_idx is within bounds");

    if(reachable_idx >= reachable.size())
      remove_edges(i);
    else if(i == reachable[reachable_idx])
      reachable_idx++;
    else
      remove_edges(i);
  }
}

/// Add to `set`, nodes that are reachable from `set`.
///
/// This implements a depth first search using a stack: at each step we pop a
/// node, and push on the stack all its successors that have not yet been
/// visited.
/// \param set: set of source nodes, must be a container with an
///   `insert(const value_type&)` method.
/// \param for_each_successor: function which given a node `n` and a function
///   `f`, applies `f` on all successors of `n`.
template <class Container, typename nodet = typename Container::value_type>
void get_reachable(
  Container &set,
  const std::function<void(
    const typename Container::value_type &,
    const std::function<void(const typename Container::value_type &)> &)>
    &for_each_successor)
{
  std::vector<nodet> stack;
  for(const auto &elt : set)
    stack.push_back(elt);

  while(!stack.empty())
  {
    auto n = stack.back();
    stack.pop_back();
    for_each_successor(n, [&](const nodet &node) {
      if(set.insert(node).second)
        stack.push_back(node);
    });
  }
}

/// Run depth-first search on the graph, starting from a single source
/// node.
/// \param src: The node to start the search from.
/// \param forwards: true (false) if the forward (backward) reachability
/// should be performed.
template<class N>
std::vector<typename N::node_indext>
grapht<N>::get_reachable(node_indext src, bool forwards) const
{
  std::vector<node_indext> src_vector;
  src_vector.push_back(src);

  return get_reachable(src_vector, forwards);
}

/// Run depth-first search on the graph, starting from multiple source
/// nodes.
/// \param src: The nodes to start the search from.
/// \param forwards: true (false) if the forward (backward) reachability
/// should be performed.
template <class N>
std::vector<typename N::node_indext> grapht<N>::get_reachable(
  const std::vector<node_indext> &src,
  bool forwards) const
{
  std::vector<node_indext> result;
  std::vector<bool> visited(size(), false);

  std::stack<node_indext, std::vector<node_indext>> s(src);

  while(!s.empty())
  {
    node_indext n = s.top();
    s.pop();

    if(visited[n])
      continue;

    result.push_back(n);
    visited[n] = true;

    const auto &node = nodes[n];
    const auto &succs = forwards ? node.out : node.in;
    for(const auto succ : succs)
      if(!visited[succ.first])
        s.push(succ.first);
  }

  return result;
}

/// Run recursive depth-limited search on the graph, starting
/// from multiple source nodes, to find the nodes reachable within n steps.
/// This function initialises the search.
/// \param src: The node to start the search from.
/// \param limit:  limit on steps
/// \return a vector of reachable node indices
template <class N>
std::vector<typename N::node_indext> grapht<N>::depth_limited_search(
  const typename N::node_indext src,
  std::size_t limit) const
{
  std::vector<node_indext> start_vector(1, src);
  return depth_limited_search(start_vector, limit);
}

/// Run recursive depth-limited search on the graph, starting
/// from multiple source nodes, to find the nodes reachable within n steps.
/// This function initialises the search.
/// \param src: The nodes to start the search from.
/// \param limit:  limit on steps
/// \return a vector of reachable node indices
template <class N>
std::vector<typename N::node_indext> grapht<N>::depth_limited_search(
  std::vector<typename N::node_indext> &src,
  std::size_t limit) const
{
  std::vector<bool> visited(nodes.size(), false);

  for(const auto &node : src)
  {
    PRECONDITION(node < nodes.size());
    visited[node] = true;
  }

  return depth_limited_search(src, limit, visited);
}

/// Run recursive depth-limited search on the graph, starting
// from multiple source nodes, to find the nodes reachable within n steps
/// \param src: The nodes to start the search from.
/// \param limit:  limit on steps
/// \param visited: vector of booleans indicating whether a node has been
///   visited
/// \return a vector of reachable node indices
template <class N>
std::vector<typename N::node_indext> grapht<N>::depth_limited_search(
  std::vector<typename N::node_indext> &src,
  std::size_t limit,
  std::vector<bool> &visited) const
{
  if(limit == 0)
    return src;

  std::vector<node_indext> next_ring;

  for(const auto &n : src)
  {
    for(const auto &o : nodes[n].out)
    {
      if(!visited[o.first])
      {
        next_ring.push_back(o.first);
        visited[o.first] = true;
      }
    }
  }

  if(next_ring.empty())
    return src;

  limit--;

  for(const auto &succ : depth_limited_search(next_ring, limit, visited))
    src.push_back(succ);

  return src;
}

/// Find connected subgraphs in an undirected graph.
/// \param [out] subgraph_nr: will be resized to graph.size() and populated
///   to map node indices onto subgraph numbers. The subgraph numbers are dense,
///   in the range 0 - (number of subgraphs - 1)
/// \return Number of subgraphs found.
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

      for(const auto &o : node.out)
      {
        if(!visited[o.first])
          s.push(o.first);
      }
    }

    nr++;
  }

  return nr;
}

template<class N>
void grapht<N>::tarjan(tarjant &t, node_indext v) const
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
      INVARIANT(
        !t.scc_stack.empty(),
        "stack of strongly connected components should have another component");
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

/// Computes strongly-connected components of a graph and yields a vector
/// expressing a mapping from nodes to components indices. For example, if nodes
/// 1 and 3 are in SCC 0, and nodes 0, 2 and 4 are in SCC 1, this will leave
/// `subgraph_nr` holding `{ 1, 0, 1, 0, 1 }`, and the function will return 2
/// (the number of distinct SCCs).
/// Lower-numbered SCCs are closer to the leaves, so in the particular case
/// of a DAG, sorting by SCC number gives a topological sort, and for a cyclic
/// graph the SCCs are topologically sorted but arbitrarily ordered internally.
/// \param [in,out] subgraph_nr: should be pre-allocated with enough storage
///   for one entry per graph node. Will be populated with the SCC indices of
///   each node.
/// \return the number of distinct SCCs.
template<class N>
std::size_t grapht<N>::SCCs(std::vector<node_indext> &subgraph_nr) const
{
  tarjant t(nodes.size(), subgraph_nr);

  for(node_indext v0=0; v0<size(); v0++)
    if(!t.visited[v0])
      tarjan(t, v0);

  return t.scc_count;
}

/// Ensure a graph is chordal (contains no 4+-cycles without an edge crossing
/// the cycle) by adding extra edges. Note this adds more edges than are
/// required, including to acyclic graphs or acyclic subgraphs of cyclic graphs,
/// but does at least ensure the graph is not chordal.
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
    for(const auto &o1 : n.out)
      for(const auto &o2 : n.out)
      {
        if(o1.first!=o2.first)
        {
          tmp.add_undirected_edge(o1.first, o2.first);
          this->add_undirected_edge(o1.first, o2.first);
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

template <typename node_index_type>
void output_dot_generic(
  std::ostream &out,
  const std::function<void(std::function<void(const node_index_type &)>)>
    &for_each_node,
  const std::function<
    void(const node_index_type &, std::function<void(const node_index_type &)>)>
    &for_each_succ,
  const std::function<std::string(const node_index_type &)> node_to_string,
  const std::function<std::string(const node_index_type &)> node_to_pretty)
{
  for_each_node([&](const node_index_type &i) {
    out << node_to_pretty(i) << ";\n";
    for_each_succ(i, [&](const node_index_type &n) {
      out << node_to_string(i) << " -> " << node_to_string(n) << '\n';
    });
  });
}

template <class N>
std::vector<typename grapht<N>::node_indext>
grapht<N>::get_successors(const node_indext &n) const
{
  std::vector<node_indext> result;
  std::transform(
    nodes[n].out.begin(),
    nodes[n].out.end(),
    std::back_inserter(result),
    [&](const std::pair<node_indext, edget> &edge) { return edge.first; });
  return result;
}

template <class N>
void grapht<N>::for_each_successor(
  const node_indext &n,
  std::function<void(const node_indext &)> f) const
{
  std::for_each(
    nodes[n].out.begin(),
    nodes[n].out.end(),
    [&](const std::pair<node_indext, edget> &edge) { f(edge.first); });
}

template <class N>
void grapht<N>::output_dot(std::ostream &out) const
{
  const auto for_each_node =
    [this](const std::function<void(const node_indext &)> &f) {
      for(node_indext i = 0; i < nodes.size(); ++i)
        f(i);
    };

  const auto for_each_succ = [&](
    const node_indext &i, const std::function<void(const node_indext &)> &f) {
    for_each_successor(i, f);
  };

  const auto to_string = [](const node_indext &i) { return std::to_string(i); };
  const auto to_pretty_string = [this](const node_indext &i) {
    return nodes[i].pretty(i);
  };
  output_dot_generic<node_indext>(
    out, for_each_node, for_each_succ, to_string, to_pretty_string);
}

#endif // CPROVER_UTIL_GRAPH_H
