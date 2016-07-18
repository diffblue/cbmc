/*******************************************************************\

Module: Lock Graph (context-sensitive)

Author: Peter Schrammel

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/config.h>
#include <util/xml_expr.h>
#include <util/xml.h>

#include "lock_graph_cs.h"

/*******************************************************************
 Function: lock_graph_cst::has_node

 Inputs:

 Outputs: whether a node exists in the graph

 Purpose: returns node index in n

\*******************************************************************/

bool lock_graph_cst::has_node(const lock_typet &lock, 
			      node_indext &n)
{
  for(node_indext i=0;i<size();i++)
  {
    if((*this)[i].lock.begin()->first == lock.begin()->first)
    {
      n = i;
      return true; 
    }
  }
  return false;
}

/*******************************************************************
 Function: lock_graph_cst::has_edge

 Inputs:

 Outputs: whether an edge exists in the graph

 Purpose: returns edge index in e

\*******************************************************************/

bool lock_graph_cst::has_edge(node_indext n1, node_indext n2,
                              const ai_cs_baset::placet &place, 
			      edge_indext &e)
{
  const nodet &node = nodes[n1];
  for(edgemapt::const_iterator it=node.out.begin();
      it!=node.out.end(); it++)
  {
    for(edgesett::const_iterator e_it=it->second.begin();
	e_it!=it->second.end(); e_it++)
    {
      if(it->first == n2 && edges[*e_it].place == place)
      {
	e = *e_it;
	return true; 
      }
    }
  }
  return false;
}

/*******************************************************************
 Function: lock_graph_cst::add_lock

 Inputs:

 Outputs:

 Purpose: adds a lock to the graph

\*******************************************************************/

void lock_graph_cst::add_lock(const namespacet &ns,
			      const lock_typet &locks_owned,
			      const ai_cs_baset::placet &place,
			      const lock_typet &locks_acquired)
{
#ifdef DEBUG
  std::cout << "ADD LOCK at " << place << ": " << std::endl;
  std::cout << "owned: ";
  lock_graph_cst::output_lock(ns,std::cout,locks_owned);
  std::cout << std::endl;
  std::cout << "acquired: ";
  lock_graph_cst::output_lock(ns,std::cout,locks_acquired);
  std::cout << std::endl;
#endif

  for(lock_typet::const_iterator to_it = locks_acquired.begin();
      to_it != locks_acquired.end(); ++to_it)
  {
    //ignore NULL objects (proper initialization should be checked by another analysis)
    if(value_sett::object_numbering[to_it->first].id()=="NULL-object")
      continue;
    
    lock_typet lock_acquired;
    lock_acquired.insert(*to_it);
    unsigned to_node_index = -1;
    bool to_node_exists = has_node(lock_acquired, to_node_index);
    if(!to_node_exists)
    {
      to_node_index = add_node();
      (*this)[to_node_index].set(lock_acquired);
    }
    (*this)[to_node_index].add(place);

    for(lock_typet::const_iterator from_it = locks_owned.begin();
	from_it != locks_owned.end(); ++from_it)
    {
      //ignore NULL objects (proper initialization should be checked by another analysis)
      if(value_sett::object_numbering[from_it->first].id()=="NULL-object")
        continue;

      lock_typet lock_owned;
      lock_owned.insert(*from_it);

      //suppress irrelevant self-loops; TODO: this should produce a warning becaause locks are used inconsistenly:         
      if(!lock_owned.is_top() &&
         lock_owned == lock_acquired)
	continue;

      unsigned from_node_index = -1;
      bool from_node_exists = has_node(lock_owned, from_node_index);
//      assert(from_node_exists); //TODO: this should actually exist at this point
      bool edge_exists = false;
      edge_indext edge_index = -1;
      if(!from_node_exists)
      {
	from_node_index = add_node();
	(*this)[from_node_index].set(lock_owned);
      }
      else
      {
	edge_exists = has_edge(from_node_index, to_node_index, 
			       place, edge_index);
      }

      if(!edge_exists)
      {
	edge_index = add_edge(from_node_index, to_node_index);
	edges[edge_index].set(place);
      }
      
      assert(edge(edge_index).place == place);
    }
  }
}  

/*******************************************************************
 Function: lock_graph_cst::closure

 Inputs:

 Outputs: 

 Purpose: adds additional edges for indeterminate locks

\*******************************************************************/

void lock_graph_cst::closure()
{
  for(node_indext n=0; n<size(); n++)
  {
    const nodet &node = (*this)[n];
    if(!node.lock.is_top())
      continue;

    const edgemapt &out = node.out;
    for(edgemapt::const_iterator it=out.begin();
	it!=out.end(); it++)
    {
      for(edgesett::const_iterator e_it=it->second.begin();
          e_it!=it->second.end(); e_it++)
      {
	for(node_indext _n=0; _n<size(); _n++)
	{
	  if(_n==n || _n==it->first)
	    continue;

	  edge_indext edge_index = -1;
	  const edget &e = edges[*e_it];
	  bool edge_exists = has_edge(_n, it->first, e.place, edge_index);
	  if(!edge_exists)
	  {
	    edge_index = add_edge(_n,it->first);
	    edges[edge_index].set(e.place);
	  }
	}      
      }
    }
    const edgemapt &in = node.in;
    for(edgemapt::const_iterator it=in.begin();
	it!=in.end(); it++)
    {
      for(edgesett::const_iterator e_it=it->second.begin();
          e_it!=it->second.end(); e_it++)
      {
	for(node_indext _n=0; _n<size(); _n++)
	{
	  if(_n==n || _n==it->first)
	    continue;

	  edge_indext edge_index = -1;
	  const edget &e = edges[*e_it];
	  bool edge_exists = has_edge(it->first, _n, e.place, edge_index);
	  if(!edge_exists)
	  {
	    edge_index = add_edge(it->first,_n);
	    edges[edge_index].set(e.place);
	  }
	}      
      }
    }
  }
} 


/*******************************************************************
 Function: lock_graph_cst::output

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_cst::output_lock(const namespacet &ns, std::ostream &out, 
		   const lock_typet &lock)
{
  for(lock_typet::const_iterator
      o_it=lock.begin();
      o_it!=lock.end();
      )
  {
    const exprt &o = value_sett::object_numbering[o_it->first];
    out << from_expr(ns, "", o);
    if(++o_it != lock.end())
      out << " ";
  }
}

void lock_graph_cst::output(const namespacet &ns,
			 std::ostream &out) const
{
  for(node_indext n=0; n<size(); n++)
  {
    assert(n<size());
    const nodet &node = (*this)[n];
    out << n << " lock ";
    lock_graph_cst::output_lock(ns,out,node.lock);
    out << std::endl << "  owned at " << node.places << std::endl;
    for(edgemapt::const_iterator it=node.out.begin();
	it!=node.out.end(); it++)
    {
      for(edgesett::const_iterator e_it=it->second.begin();
          e_it!=it->second.end(); ++e_it)
      {
        assert(*e_it<edges.size());
	out << "  acquired " << edges[*e_it].place << std::endl 
	    << "  -> " << it->first << std::endl;
      }
    }
  }
}

/*******************************************************************
 Function: lock_graph_cst::convert

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_cst::convert_node(const namespacet &ns,
				  xmlt &dest,
				  node_indext n)
{
  assert(n<size());
  xmlt &node = dest.new_element("node");
  node.set_attribute("id",n);
  std::ostringstream ss; 
  lock_graph_cst::output_lock(ns,ss,(*this)[n].lock);
  node.data = ss.str(); //xmlt::escape(ss.str());
}

void lock_graph_cst::convert_edge(const namespacet &ns,
				  xmlt &dest,
				  node_indext n,
				  node_indext m,
				  edge_indext e)
{
  assert(e<edges.size());
  xmlt &ee=dest.new_element("edge");
  ee.set_attribute("from",n);
  ee.set_attribute("to",m);
  ee.set_attribute("nr",e);
  std::ostringstream ss; 
  ss << edges[e].place;
  ee.data = ss.str(); //xmlt::escape(ss.str());
}

void lock_graph_cst::convert(const namespacet &ns,
			     xmlt &dest)
{
  dest = xmlt("lock-graph");
  for(node_indext n=0; n<size(); n++)
  {
    convert_node(ns,dest,n);
    const nodet &node = (*this)[n];
    for(edgemapt::const_iterator it=node.out.begin();
	it!=node.out.end(); it++)
    {
      for(edgesett::const_iterator e_it=it->second.begin();
          e_it!=it->second.end(); e_it++)
      {
	convert_edge(ns,dest,n,it->first,*e_it);
      }
    }
  }
}

