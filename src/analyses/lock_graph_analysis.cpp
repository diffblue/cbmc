/*******************************************************************\

Module: Lock graph

Author: Peter Schrammel

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/config.h>
#include <util/xml_expr.h>
#include <util/xml.h>
#include <util/graph_dominators.h>

#include "lock_graph_analysis.h"

/*******************************************************************
 Function: lock_graph_domaint::transform

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_domaint::transform(locationt from_l,
				   locationt to_l,
				   ai_baset &ai,
				   const namespacet &ns)
{
  lock_graph_analysist &lock_graph_analysis = static_cast<lock_graph_analysist &>(ai);

  switch (from_l->type)
  {
  case FUNCTION_CALL:
  {
    const code_function_callt &code = to_code_function_call(from_l->code);

    const exprt &function = code.function();

    if (function.id() == ID_symbol)
    {
      const irep_idt& function_name = to_symbol_expr(function).get_identifier();

#ifdef DEBUG
      std::cout << "CALL: " << function_name << std::endl;
#endif

      bool lock = function_name == config.ansi_c.lock_function;
      bool unlock = function_name == config.ansi_c.unlock_function;

      if (lock || unlock)
      {
	// retrieve argument
        // ASSUMPTION: lock is in the first argument
	assert(code.arguments().size() >= 1);
	exprt arg = code.arguments()[0];
#ifdef DEBUG
	std::cout << "ARG: " << from_expr(ns,"",arg) << std::endl;
#endif
	value_sett::object_mapt new_objects, lock_objects;
	lock_graph_analysis.lock_set_analysis.value_set_analysis[from_l].
	  value_set.get_value_set(arg, new_objects, ns, false);
	lock_set_domaint::clean_update(new_objects,lock_objects);
	assert(lock_objects.read().size() != 0);

	//FUTURE: This could be made more precise by tracking
	// the acquisition and release of non-determined,
	// but non-top locks in the lock graph
	if(lock_objects.read().size()>1) //merge non-determined locks
	{
#ifdef DEBUG
  	  std::cout << "MERGE" << std::endl;
#endif
	  lock_objects.write().make_top();
	  assert(lock_objects.read().size()==1);
	}

	which_threads_internalt::thread_categoriest thread_categories;
	if(lock_graph_analysis.which_threads.is_thread_entry(from_l->function))
        {
	  thread_categories[from_l->function] = 
	    lock_graph_analysis.which_threads.thread_categories[from_l->function];
        }
        else
	{
	  lock_graph_analysis.which_threads.used_by_thread_categories(from_l->function,
						 thread_categories);
	}
#ifdef DEBUG
	std::cout << "THREADS:";
	for(which_threads_internalt::thread_categoriest::const_iterator 
	      t_it = thread_categories.begin();
	    t_it != thread_categories.end(); ++t_it)
	{
	  std::cout << " " << t_it->first;
	}
	std::cout << std::endl;
#endif

	//FUTURE: Rather than built globally,
	//in a thread-sensitive analysis, the graph should be built
	//for each function and thread and assembled on merge/join...
	//This will require a thread-aware call graph recursion...
	for(which_threads_internalt::thread_categoriest::const_iterator 
	      t_it = thread_categories.begin();
	    t_it != thread_categories.end(); ++t_it)
	{
	  if(lock) push_lock(ns,lock_graph_analysis,t_it->first,lock_objects.read());
	  if(unlock) pop_lock(ns,lock_graph_analysis,t_it->first,lock_objects.read());
	}
      } 
    } // if symbol
  } // case switch
  default:
    break;
	
  } // switch
}

/*******************************************************************
 Function: lock_graph_domaint::has_node

 Inputs:

 Outputs: whether a node exists in the graph

 Purpose: returns node index in n

\*******************************************************************/

bool lock_graph_domaint::has_node(const grapht &_graph, const nodet &node, 
				  grapht::node_indext &n)
{
  for(grapht::node_indext i=0;i<_graph.size();i++)
  {
    if((node.is_thread && _graph[i].is_thread &&
	_graph[i].thread_category == node.thread_category) ||
       (!node.is_thread && !_graph[i].is_thread &&
	_graph[i].lock.begin()->first == node.lock.begin()->first)
      ) 
    {
      n = i;
      return true; 
    }
  }
  return false;
}

/*******************************************************************
 Function: lock_graph_domaint::push_lock

 Inputs:

 Outputs:

 Purpose: adds a lock to the graph

\*******************************************************************/

void lock_graph_domaint::push_lock(const namespacet &ns,
				   lock_graph_analysist &lock_graph_analysis,
				   irep_idt thread_category,
				   const lock_typet &lock) 
{
  assert(lock.size() == 1); 

#ifdef DEBUG
  std::cout << "PUSH LOCK: "; output_lock(ns,std::cout,lock);
  std::cout << std::endl;
#endif

  assert(!lock_graph_analysis.current_locks[thread_category].empty());
  unsigned prev_index = lock_graph_analysis.current_locks[thread_category].back();
  nodet node(lock);
  std::size_t node_index = -1;
  bool node_exists = has_node(lock_graph_analysis.lock_graph,node,node_index);
  bool edge_exists = false;
  
  if(!node_exists)
  {
    node_index = lock_graph_analysis.lock_graph.add_node(node);
  }
  else
  {
    edge_exists = lock_graph_analysis.lock_graph.has_edge(prev_index,node_index);
  }

  if(!edge_exists)
  {
    lock_graph_analysis.lock_graph.add_edge(prev_index,node_index);
    lock_graph_analysis.lock_graph.edge(prev_index,node_index) = edget(thread_category);
    assert(lock_graph_analysis.lock_graph.has_edge(prev_index,node_index));
    assert(lock_graph_analysis.lock_graph[prev_index].out.size()>0);
  }
  else
  {
    lock_graph_analysis.lock_graph.edge(prev_index,node_index).
      thread_categories.insert(thread_category);
  }

#ifdef DEBUG
  std::cout << "node exists: " << node_exists << std::endl;
  std::cout << "node index: " << node_index << std::endl;
  std::cout << "prev index: " << prev_index << std::endl;
  std::cout << "edge exists: " << edge_exists << std::endl;
#endif

  lock_graph_analysis.current_locks[thread_category].push_back(node_index);
}  

/*******************************************************************
 Function: lock_graph_domaint::pop_lock

 Inputs:

 Outputs:

 Purpose: moves up in the lock hierarchy

\*******************************************************************/

void lock_graph_domaint::pop_lock(const namespacet &ns,
				  lock_graph_analysist &lock_graph_analysis,
				  irep_idt thread_category,
				  const lock_typet &lock) 
{
  assert(lock.size() == 1);

#ifdef DEBUG
  std::cout << "POP LOCK: "; output_lock(ns,std::cout,lock);
  std::cout << std::endl;
#endif

  std::list<typename lock_graph_domaint::grapht::node_indext>
    &locks = lock_graph_analysis.current_locks[thread_category];

  assert(!locks.empty());
  unsigned current_index = locks.back();
  if(!lock.top && lock_graph_analysis.lock_graph[current_index].lock != lock)
  {
#ifdef DEBUG
    std::cout << "warning: acquire-release order violation: thread category "
	      << thread_category << ", lock ";
    lock_graph_domaint::output_lock(ns,std::cout,lock);
    std::cout << ", expected lock ";
    lock_graph_domaint::output_lock(ns,std::cout,
				    lock_graph_analysis.lock_graph[current_index].lock);
    std::cout << std::endl;
#endif
    assert(!locks.empty());
    std::list<typename lock_graph_domaint::grapht::node_indext>::iterator  
      l_it = locks.end();
    do
    {
      --l_it;
      if(lock_graph_analysis.lock_graph[*l_it].lock == lock)
      {
	locks.erase(l_it);
	break;
      }
    }
    while(l_it != locks.begin());
  }
  else
  {
    locks.pop_back();
  }
}

/*******************************************************************
 Function: lock_grapht::detect_deadlocks

 Inputs:

 Outputs:

 Purpose: detects cycles that are not dominated by other locks

\*******************************************************************/

void lock_graph_analysist::detect_deadlocks()
{
  for(lock_graph_domaint::grapht::node_indext n=0; n<lock_graph.size(); n++)
  {
    // find cycles
    lock_graph_domaint::grapht::patht path;
    lock_graph.shortest_loop(n,path);
    if(path.size() < 1) 
      continue;

    // make it a cycle
    path.push_back(path.front());
    // check whether more than one thread is involved in the cycle
    std::set<irep_idt> thread_categories;
    lock_graph_domaint::grapht::patht::const_iterator
      p_it = path.begin(), pp_it = p_it++;
#ifdef DEBUG
    std::cout << "CYCLE: " << *pp_it;
#endif
    for( ; p_it != path.end(); pp_it = p_it++)
    {
#ifdef DEBUG
      std::cout << " " << *p_it;
#endif
      assert(lock_graph.has_edge(*pp_it,*p_it));
      const std::set<irep_idt> &tc = 
	lock_graph.edge(*pp_it,*p_it).thread_categories;
      assert(!tc.empty());
      thread_categories.insert(tc.begin(),tc.end());
    }
#ifdef DEBUG
    std::cout << std::endl;
#endif
    bool more_than_one = thread_categories.size() > 1;
#ifdef DEBUG
    std::cout << "categories: " << thread_categories.size() << std::endl;
#endif
    if(!more_than_one) //check spawn cardinality of category
    {
      const which_threads_internalt::thread_categoryt &t =
	which_threads.thread_categories[*thread_categories.begin()];
      more_than_one = t.k>1 || t.inside_loop;
    }
    if(!more_than_one) 
      continue;

    // check whether the cycle is not dominated by a gatelock
    std::set<lock_graph_domaint::grapht::node_indext> dominators;
    graph_dominators_templatet<lock_graph_domaint::grapht,false> 
      graph_dominators;
    for(std::set<irep_idt>::const_iterator 
	t_it = thread_categories.begin();
	t_it != thread_categories.end(); ++t_it)
    {
      lock_graph_domaint::grapht::nodet node(*t_it);
      lock_graph_domaint::grapht::node_indext node_index = -1;
      bool node_exists = 
	lock_graph_domaint::has_node(lock_graph,node,node_index);
      assert(node_exists);

      //dominators for each entry node (thread category)
      //  Intuitively, we should project the graph on each
      //    thread category, compute the dominators over that graph
      //    and then intersect; but since there must be a unique
      //    gatelock (chain), I think that it should not matter.
      graph_dominators(lock_graph,node_index);
#ifdef DEBUG
      std::cout << graph_dominators;
#endif
      lock_graph_domaint::grapht::patht::const_iterator
	p_it = path.begin();
      if(dominators.size()==0)
      { //initialize
	dominators.insert(graph_dominators.dominators[*p_it].begin(),
			  graph_dominators.dominators[*p_it].end());
        //remove path nodes (otherwise causes problem with self-loops)
	for(lock_graph_domaint::grapht::patht::const_iterator
	      pp_it = path.begin() ; pp_it != path.end(); pp_it++)
	{
	  std::set<lock_graph_domaint::grapht::node_indext>::iterator
	    d_it = dominators.find(*pp_it);
	  if(d_it != dominators.end())
  	    dominators.erase(d_it);
	}

	++p_it;
      }
      for(; p_it != path.end(); ++p_it)
      { //intersect over dominating nodes for all cycle nodes
	graph_dominators_templatet<lock_graph_domaint::grapht,false>::
	  set_intersect(dominators,graph_dominators.dominators[*p_it],-1);
	if(dominators.size()==0) 
	  break;
      }
      if(dominators.size()==0) 
	break;
    }
    if(dominators.size()>0) //has a gatelock (chain)
      continue;

    potential_deadlocks.push_back(path);
  }
}

/*******************************************************************
 Function: lock_graph_domaint::output

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_domaint::output_lock(const namespacet &ns, std::ostream &out, 
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

void lock_graph_domaint::output_thread_categories(std::ostream &out,
			     const std::set<irep_idt> &thread_categories)
{
  std::set<irep_idt>::const_iterator 
	t_it = thread_categories.begin();
  while(true)
  {
    out << *t_it;
    ++t_it;
    if(t_it == thread_categories.end())
       break;
    out << " ";
  }
}

void lock_graph_analysist::output(const namespacet &ns,
			 const goto_functionst &goto_functions,
			 std::ostream &out) const
{
  for(lock_graph_domaint::grapht::node_indext n=0; n<lock_graph.size(); n++)
  {
    const lock_graph_domaint::nodet &node = lock_graph[n];
    if(node.is_thread) 
      out << n << " thread category " << node.thread_category << ":" << std::endl;
    else
    {
      out << n << " lock ";
      lock_graph_domaint::output_lock(ns,out,node.lock);
      out << std::endl;
    }
    for(lock_graph_domaint::grapht::edgest::const_iterator
	  it=node.out.begin();
	it!=node.out.end();
	it++)
    {
      const std::set<irep_idt> &thread_categories = 
	lock_graph.edge(n,it->first).thread_categories;
      out << "[ ";
      lock_graph_domaint::output_thread_categories(out,thread_categories);
      out << " ] -> " << it->first << std::endl;
    }
  }
}

/*******************************************************************
 Function: lock_graph_analysist::output_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysist::output_deadlocks(const namespacet &ns,
				   std::ostream &out)
{
  out << "* potential deadlocks    " << potential_deadlocks.size() << std::endl;

  for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
      d_it != potential_deadlocks.end(); ++d_it)
  {
    lock_graph_domaint::grapht::patht::const_iterator
      p_it = d_it->begin(), pp_it = p_it++;
    out << "  " << *pp_it;
    for( ; p_it != d_it->end(); pp_it = p_it++)
    {
      assert(lock_graph.has_edge(*pp_it,*p_it));
      const std::set<irep_idt> &tc = 
	lock_graph.edge(*pp_it,*p_it).thread_categories;
      out << " -[ ";
      lock_graph_domaint::output_thread_categories(out,tc);
      out << " ]-> " << *p_it;
    }
    out << std::endl;
  }
}

/*******************************************************************
 Function: lock_graph_analysist::convert

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysist::convert_node(const namespacet &ns,
			       xmlt &dest,
			       lock_graph_domaint::grapht::node_indext n)
{
  xmlt &node = dest.new_element("node");
  node.set_attribute("id",n);
  std::ostringstream ss; 
  if(lock_graph[n].is_thread) 
  {
    node.set_attribute("is_thread","true");
    node.data = id2string(lock_graph[n].thread_category);
  }
  else
  {
    node.set_attribute("is_thread","false");
    lock_graph_domaint::output_lock(ns,ss,lock_graph[n].lock);
    node.data = ss.str(); //xmlt::escape(ss.str());
  }
}

void lock_graph_analysist::convert_edge(const namespacet &ns,
			       xmlt &dest,
			       lock_graph_domaint::grapht::node_indext n,
			       lock_graph_domaint::grapht::node_indext m)
{
  xmlt &e=dest.new_element("edge");
  e.set_attribute("from",n);
  e.set_attribute("to",m);
  std::ostringstream ss; 
  lock_graph_domaint::output_thread_categories(ss,
    lock_graph.edge(n,m).thread_categories);
  e.data = ss.str(); //xmlt::escape(ss.str());
}

void lock_graph_analysist::convert(const namespacet &ns,
			  const goto_functionst &goto_functions,
			  xmlt &dest)
{
  dest = xmlt("lock-graph");
  for(lock_graph_domaint::grapht::node_indext n=0; n<lock_graph.size(); n++)
  {
    convert_node(ns,dest,n);
    const lock_graph_domaint::nodet &node = lock_graph[n];
    for(lock_graph_domaint::grapht::edgest::const_iterator
	  it=node.out.begin();
	it!=node.out.end();
	it++)
    {
      convert_edge(ns,dest,n,it->first);
    }
  }
}

/*******************************************************************
 Function: lock_graph_analysist::convert_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysist::convert_deadlocks(const namespacet &ns,
				    xmlt &dest)
{
  dest = xmlt("deadlock-analysis");
  for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
      d_it != potential_deadlocks.end(); ++d_it)
  {
    xmlt &d=dest.new_element("potential-deadlock");
    lock_graph_domaint::grapht::patht::const_iterator
      p_it = d_it->begin(), pp_it = p_it++;
    for( ; p_it != d_it->end(); pp_it = p_it++)
    {
      assert(lock_graph.has_edge(*pp_it,*p_it));
      convert_edge(ns,d,*pp_it,*p_it);
      convert_node(ns,d,*pp_it);
    }
  }
}

/*******************************************************************
 Function: show_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void show_deadlocks(const namespacet &ns,
		    ui_message_handlert::uit ui,
		    const goto_functionst &goto_functions,
		    lock_graph_analysist &lock_graph_analysis)
{
  switch (ui)
  {
  case ui_message_handlert::XML_UI:
  {
    xmlt xml;
    lock_graph_analysis.convert_deadlocks(ns,xml);
    std::cout << xml << std::endl;
  }
  break;

  case ui_message_handlert::PLAIN:
    lock_graph_analysis.output_deadlocks(ns,std::cout);
    break;

  default:
    ;
  }
}

