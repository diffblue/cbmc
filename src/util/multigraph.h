/*******************************************************************\

Module: A Template Class for Graphs with Multiple Edges

Author: Peter Schrammel

\*******************************************************************/

#ifndef __MULTIGRAPH_H
#define __MULTIGRAPH_H

//#define DEBUG

#define BACKTRACK_ON_BAD_CYCLE
#define BAD_SUB_CYCLE_CHECK
#define BAD_SUB_CYCLE_CHECK_MAX 3
#define USE_TRIE
#define NO_PERMUTATIONS

#include <list>
#include <stack>
#include <map>
#include <vector>
#include <ostream>
#include <cassert>

#ifdef USE_TRIE
#include "trie.h"
#endif

#include "graph.h"

template<class E=empty_edget>
  class multigraph_nodet
{
public:
typedef unsigned node_indext;
typedef unsigned edge_indext;

typedef E edget;
typedef std::set<edge_indext> edgesett;
typedef std::map<node_indext, edgesett> edgemapt;

edgemapt in, out;
  
inline void add_in(node_indext n, edge_indext e)
{
  in[n].insert(e);
}
  
inline void add_out(node_indext n, edge_indext e)
{
  out[n].insert(e);
}

inline void erase_in(node_indext n, edge_indext e)
{
  edgemapt::iterator it = in.find(n);
  if(it==in.end())
    return;

  edgesett::iterator e_it = it->second.find(e);
  if(e_it==it->second.end())
    return;

  it->second.erase(e_it);
}
  
inline void erase_out(node_indext n, edge_indext e)
{
  edgemapt::iterator it = out.find(n);
  if(it==out.end())
    return;

  edgesett::iterator e_it = it->second.find(e);
  if(e_it==it->second.end())
    return;

  it->second.erase(e_it);
}
};

// a generic graph class with a parametric node type  
template<class N=multigraph_nodet<empty_edget> >
  class multigrapht
{
public:
typedef N nodet;
typedef typename nodet::node_indext node_indext;
typedef typename nodet::edget edget;
typedef typename nodet::edge_indext edge_indext;
typedef std::vector<nodet> nodest;
typedef std::vector<edget> edgest;
typedef typename nodet::edgesett edgesett;
typedef typename nodet::edgemapt edgemapt;

protected:
nodest nodes;
edgest edges;
  
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
  
inline void swap(multigrapht &other)
{
  nodes.swap(other.nodes);
  edges.swap(other.edges);
}

inline bool has_edge(node_indext i, node_indext j, edge_indext e) const
{
  return nodes[i].out.find(j)!=nodes[i].out.end() &&
  nodes[i].out[j].find(e)!=nodes[i].out[j].end();
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
  
inline const edgemapt &in(node_indext n) const
{
  return nodes[n].in;
}

inline const edgemapt &out(node_indext n) const
{
  return nodes[n].out;
}
  
inline edge_indext add_edge(node_indext a, node_indext b)
{
  unsigned no = edges.size();
  edges.push_back(edget());
  nodes[a].add_out(b,no);
  nodes[b].add_in(a,no);
  return no;
}
  
inline void remove_edge(node_indext a, node_indext b, const edget& e)
{
  nodes[a].erase_out(b,e);
  nodes[b].erase_in(a,e);
}

inline node_indext pred_node(edge_indext e)
{
  for(node_indext n=0; n<nodes.size(); n++)
  {
    const nodet &node = nodes[n];
    for(typename edgemapt::const_iterator it=node.in.begin();
	it!=node.in.end(); it++)
    {
      if(it->second.find(e)!=it->second.end())
	return it->first;
    }
  }
  assert(false);
}

inline node_indext succ_node(edge_indext e)
{
  for(node_indext n=0; n<nodes.size(); n++)
  {
    const nodet &node = nodes[n];
    for(typename edgemapt::const_iterator it=node.out.begin();
	it!=node.out.end(); it++)
    {
      if(it->second.find(e)!=it->second.end())
	return it->first;
    }
  }
  assert(false);
}
  
inline edget &edge(edge_indext e)
{
  return edges[e];
}
inline const edget &edge(edge_indext e) const
{
  return edges.at(e);
}

inline edgesett &edge(node_indext a, node_indext b)
{
  return nodes[a].out[b];
}
inline const edgesett &edge(node_indext a, node_indext b) const
{
  return nodes[a].out.at(b);
}

edge_indext add_undirected_edge(node_indext a, node_indext b);
void remove_undirected_edge(node_indext a, node_indext b, edge_indext e);
  
inline void remove_edges(node_indext n)
{
  remove_in_edges(n);
  remove_out_edges(n);
}
  
inline void clear()
{
  nodes.clear();
}
  
typedef std::list<edge_indext> patht;
typedef std::set<patht> pathst;

class cycle_visitort 
{
public:
  //returns true if cycle enumeration shall be aborted
  //  sets the bool to true if super-cycles shall not be visited
  virtual bool visit(const patht &, bool&)=0;
};

void cycles(cycle_visitort &visitor) const;

};

/*******************************************************************\

Function: multigrapht::add_undirected_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
typename multigrapht<N>::edge_indext multigrapht<N>::add_undirected_edge(node_indext a, node_indext b)
{
  assert(a<nodes.size());
  assert(b<nodes.size());
  nodet &na=nodes[a];
  nodet &nb=nodes[b];
  edge_indext e = add_edge(a,b);
  na.add_out(b,e);
  nb.add_in(a,e);
}

/*******************************************************************\

Function: multigrapht::remove_undirected_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N> 
void multigrapht<N>::remove_undirected_edge(node_indext a, node_indext b, edge_indext e)
{
  nodet &na=nodes[a];
  nodet &nb=nodes[b];
  na.out.erase(b,e);
  nb.out.erase(a,e);
  na.in.erase(b,e);
  nb.in.erase(a,e);
  edges.erase(e);
}

/*******************************************************************\

Function: multigrapht::cycles

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class N>
void multigrapht<N>::cycles(
  cycle_visitort &visitor) const
{
  std::vector<bool> visited_nodes;
  typedef std::vector<node_indext> node_patht;

  //stack of edges followed
  struct stack_elementt {
    node_patht node_path;
    std::set<edge_indext> followed_edges;
    patht path;
  };
  std::stack<stack_elementt> stack;

#ifdef BAD_SUB_CYCLE_CHECK
#ifdef USE_TRIE
  typedef trie<edge_indext ,bool, false> bad_cyclest;
#else
  typedef std::set<patht> bad_cyclest;
#endif  
  bad_cyclest bad_cycles;
#endif

  // initialization
  visited_nodes.resize(nodes.size(), false);

  // for each SCC:
  for(node_indext src=0; src<size(); src++)
  {
#ifdef DEBUG
    std::cout << "visited node " << src << ": " << visited_nodes[src] << std::endl;
#endif
    if(visited_nodes[src]) continue;

    visited_nodes[src] = true;
    stack.push(stack_elementt());
    stack.top().node_path.push_back(src);

#ifdef BACKTRACK_ON_BAD_CYCLE
    bool backtracked = false;
#endif
    while(!stack.empty())
    {
      stack_elementt &s = stack.top();
      typename node_patht::iterator n = --s.node_path.end();

#ifdef DEBUG
      std::cout << "node path:";
      for(typename node_patht::iterator n_it = s.node_path.begin();
	  n_it != s.node_path.end(); ++n_it)
        std::cout << " " << *n_it;
      std::cout << std::endl;
      std::cout << "edge path:";
      for(typename patht::iterator e_it = s.path.begin();
	  e_it != s.path.end(); ++e_it)
	std::cout << " " << *e_it;
      std::cout << std::endl;
#endif

      // check whether there is a cycle
#ifdef BACKTRACK_ON_BAD_CYCLE
      if(backtracked) backtracked = false;
      else
#endif
      if(!s.path.empty())
      {
        patht p = s.path;
        assert(p.size()==s.node_path.size()-1);
        for(typename node_patht::iterator n_it = s.node_path.begin();
	    n_it != n; ++n_it)
        {
          if(*n_it == *n)
          {
#ifdef DEBUG
	    std::cout << "cycle found!" << std::endl;
#endif
	    //call callback
            bool bad = false;
	    if(visitor.visit(p, bad))
	      return;
#ifdef BACKTRACK_ON_BAD_CYCLE
	    if(bad)
	    {
#ifdef DEBUG
   	      std::cout << "new bad cycle" << std::endl;
#endif
	      //backtrack
	      stack.pop();
	      backtracked = true;
#ifdef BAD_SUB_CYCLE_CHECK
	      if(p.size()<=BAD_SUB_CYCLE_CHECK_MAX)
#ifdef USE_TRIE
	      {
#ifdef NO_PERMUTATIONS
		p.sort();
#else
		p.reverse(); //we are interested in suffixes
#endif
		bad_cycles.insert(p, true);
	      }
#else
  	        bad_cycles.insert(p);
#ifdef DEBUG
   	      std::cout << "bad cycles: " << bad_cycles.size() << std::endl;
#endif
#endif
#endif
	    }
#endif
	    break;
	  }
	  p.pop_front();
	}
      }

#ifdef BACKTRACK_ON_BAD_CYCLE
      if(backtracked) continue;
#endif

      // follow edge
      const nodet &node=nodes[*n];
      bool found = false;
      for(typename edgemapt::const_iterator it=node.out.begin();
          it!=node.out.end(); it++)
      {
        for(typename edgesett::const_iterator e_it=it->second.begin();
	    e_it!=it->second.end(); e_it++)
	{
#ifdef DEBUG
	  std::cout << "edge? " << *e_it << std::endl;
#endif
          // don't follow an edge twice at this point of the exploration
          // don't use an edge twice on the same path
          if(s.followed_edges.find(*e_it) == s.followed_edges.end())
          {
            bool used_twice = false;
            for(typename patht::const_iterator p_it = s.path.begin();
                p_it != s.path.end(); ++p_it)
            {
              if(*p_it == *e_it)
              {
                used_twice = true;
                break;
              }
            }

            if(!used_twice)
            {
#ifdef BAD_SUB_CYCLE_CHECK
              //check for bad cycle suffixes
	      bool bad = false;
	      patht new_path = s.path; new_path.push_back(*e_it);
#ifdef USE_TRIE
#ifdef NO_PERMUTATIONS
	      new_path.sort();
	      if(bad_cycles.find_sub_of(new_path))
#else
	      new_path.reverse(); //we are interested in suffixes
	      if(bad_cycles.find_prefix_of(new_path))
#endif
	      {
#ifdef DEBUG
    	        std::cout << "old bad cycle" << std::endl;
#endif
	        bad = true;
	      }
#else
	      for(typename std::set<patht>::const_iterator 
                  b_it = bad_cycles.begin();
  	        b_it != bad_cycles.end(); ++b_it)
	      {
	        if(b_it->size()>new_path.size())
	  	  continue;

#ifdef DEBUG
		std::cout << "compare bad cycle:";
		for(typename patht::const_iterator e_it = b_it->begin();
  	            e_it != b_it->end(); ++e_it)
		  std::cout << " " << *e_it;
		std::cout << std::endl;
		std::cout << "with new cycle:   ";
		for(typename patht::const_iterator e_it = new_path.begin();
  	            e_it != new_path.end(); ++e_it)
		  std::cout << " " << *e_it;
		std::cout << std::endl;
#endif
                typename patht::const_iterator p_it1 = b_it->end();
                typename patht::const_iterator p_it2 = new_path.end();
		bool equal = true;
	        do
		{
                  --p_it1; --p_it2; 
		  if(*p_it1 != *p_it2)
		  {
		    equal = false;
	            break;
	          }
	        }
		while(p_it1 != b_it->begin());
		if(equal)
		{
#ifdef DEBUG
      	          std::cout << "old bad cycle" << std::endl;
#endif
	          bad = true;
		  break;
		}
	      }
#endif              
	      if(!bad) //now everything is fine
#endif
	      {
#ifdef DEBUG
	        std::cout << "follow edge: " << *e_it << std::endl;
#endif
                s.followed_edges.insert(*e_it);
                stack.push(stack_elementt());
                stack_elementt &new_s = stack.top();
                new_s.path = s.path;
                new_s.path.push_back(*e_it);
                new_s.node_path = s.node_path;
                new_s.node_path.push_back(it->first);
                visited_nodes[it->first] = true;
                found = true;
                break;
	      }
	    }
	  }
	}

        if(found)
          break;
      }

      if(!found)
      {
        stack.pop();
#ifdef DEBUG
	std::cout << "no edge to follow" << std::endl;
#endif
      }
    } // end while
  }
}

#endif
