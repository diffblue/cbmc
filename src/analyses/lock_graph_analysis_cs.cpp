/*******************************************************************\

Module: Lock graph analysis (context-sensitive)

Author: Peter Schrammel

\*******************************************************************/

//#define DEBUG

#define ONLY_FIRST_DEADLOCK
#define NONCONCURRENT_CHECK

#ifdef DEBUG
#include <iostream>
#endif

#include <algorithm>

#include <util/config.h>
#include <util/xml_expr.h>
#include <util/xml.h>
#include <util/graph_dominators.h>

#include "lock_graph_analysis_cs.h"
#include "ai_cs_stack.h"

/*******************************************************************
 Function: lock_graph_cs_domaint::transform

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_cs_domaint::transform(locationt from_l,
				      locationt to_l,
				      const ai_cs_stackt &stack,
				      ai_cs_baset &ai,
				      const namespacet &ns)
{
  lock_graph_analysis_cst &lock_graph_analysis =
    static_cast<lock_graph_analysis_cst &>(ai);

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
      std::cout << "CALL: " << function_name 
	        << " at " << stack
		<< std::endl;
#endif
      lock_graph_analysis.statistics.threads.insert(
	lock_graph_analysis.get_thread_id(stack));
      
      if (function_name == config.ansi_c.lock_function)
      {
	lock_graph_analysis.statistics.no_lock_operations++;
	
	// retrieve argument
        // ASSUMPTION: lock is in the first argument
	assert(code.arguments().size() >= 1);
	exprt arg = code.arguments()[0];
#ifdef DEBUG
	std::cout << "ARG: " << from_expr(ns,"",arg) << std::endl;
#endif
	ai_cs_baset::placet place(stack,from_l);
	const value_sett::object_mapt &locks_owned =
	  lock_graph_analysis.lock_set_analysis[place].object_map;
	const value_sett::object_mapt &locks_to =
	  lock_graph_analysis.lock_set_analysis[ai_cs_baset::placet(stack,to_l)].object_map;

	value_sett::object_mapt locks_acquired;
	lock_graph_analysis.lock_set_analysis.value_set_analysis[place].
	  base.value_set.get_value_set(arg, locks_acquired, ns, false);
	assert(!locks_acquired.read().empty());

	for(value_sett::object_map_dt::const_iterator it = locks_acquired.read().begin();
	    it != locks_acquired.read().end(); ++it)
	{
	  if(value_sett::object_map_dt::is_top(*it))
	    lock_graph_analysis.statistics.no_indet_lock_operations++;
	}
	
	lock_graph_analysis.graph.add_lock(ns,locks_owned.read(),place,locks_acquired.read());

	lock_graph_analysis.statistics.size_largest_lock_set =
	  std::max(lock_graph_analysis.statistics.size_largest_lock_set,
		   locks_to.read().size());
      } 
    } // if symbol
  } // case switch
  default:
    break;
	
  } // switch
}

/*******************************************************************
 Function: lock_graph_cst::detect_deadlocks

 Inputs:

 Outputs:

 Purpose: detects cycles that are not dominated by other locks

\*******************************************************************/

void lock_graph_analysis_cst::detect_deadlocks()
{
  graph.cycles(cycle_visitor);
}

/*******************************************************************
 Function: lock_graph_analysis_cst::cycle_visitort::visit

 Inputs:

 Outputs:

 Purpose: callback function from multigraph cycle enumerator

\*******************************************************************/

bool lock_graph_analysis_cst::cycle_visitort::visit(
  const lock_graph_cst::patht &cycle, bool &filter_out)
{
  super.statistics.no_cycles++;

  filter_out = false;
  if(cycle.size() < 2) 
    return false;

  if(super.potential_deadlocks.find(cycle) 
      != super.potential_deadlocks.end())
    return false;

  if(!super.check_cycle(cycle))
    return false;
    
  filter_out = true;
  super.potential_deadlocks.insert(cycle);

#ifdef ONLY_FIRST_DEADLOCK
  return true;
#else
  return false;
#endif
}

/*******************************************************************
 Function: lock_graph_analysis_cst::check_cycle

 Inputs:

 Outputs:

 Purpose: check cycles w.r.t. happens-before information 
          and multiple threads

\*******************************************************************/

bool lock_graph_analysis_cst::check_cycle(
  const lock_graph_cst::patht &cycle)
{
  for(lock_graph_cst::patht::const_iterator p_it1 = cycle.begin();
      p_it1 != cycle.end(); ++p_it1)
  {
    lock_graph_cst::patht::const_iterator p_it2 = p_it1;
    for(++p_it2;
	p_it2 != cycle.end(); ++p_it2)
    {
      // if it is the same thread, then it must be created in a loop
      const ai_cs_stackt &thread_id1 = 
        get_thread_id(graph.edge(*p_it1).place.first);
      const ai_cs_stackt &thread_id2 = 
        get_thread_id(graph.edge(*p_it2).place.first);

      if(thread_id1==thread_id2)
      {
        if(thread_id1.frames.empty())
          return false;

#ifdef DEBUG
        std::cout << "is_in_loop "
          << thread_id1.frames.back() << ": " << std::endl;
#endif
        if(is_in_loop(thread_id1, std::get<1>(thread_id1.frames.back())))
        {
#ifdef DEBUG
	       std::cout << "  yes" << std::endl;
#endif
          continue;
        }
#ifdef DEBUG
        std::cout << "  no" << std::endl;
#endif
        return false;
      }

#ifdef NONCONCURRENT_CHECK
      //else it should be concurrent
#ifdef DEBUG
      std::cout << "NON-CONCURRENT? " << std::endl;
      std::cout << "  " << graph.edge(*p_it1).place << std::endl;
      std::cout << "  " << graph.edge(*p_it2).place << std::endl;
#endif
      statistics.no_non_concurrent_checks++;
      if(non_concurrent.non_concurrent(graph.edge(*p_it1).place,
				       graph.edge(*p_it2).place))
      {
#ifdef DEBUG
	std::cout << "  yes, non-concurrent" << std::endl;
#endif
	return false;
      }
#ifdef DEBUG
      std::cout << "  no, concurrent" << std::endl;
#endif
#endif
    }
  }
  return true;
}

/*******************************************************************
 Function: lock_graph_cst::output_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysis_cst::output_deadlocks(const namespacet &ns,
				   std::ostream &out)
{
  out << "* potential deadlocks    " 
      << potential_deadlocks.size() << std::endl;

  for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
      d_it != potential_deadlocks.end(); ++d_it)
  {
    out << "  ";
    for(lock_graph_cst::patht::const_iterator
	  p_it = d_it->begin(); p_it != d_it->end(); ++p_it)
    {
      if(p_it == d_it->begin())
	out << graph.pred_node(*p_it);
      out << " - ";
      out << graph.edge(*p_it).place;
      out << " -> " << graph.succ_node(*p_it);
    }
    out << std::endl;
  }
}

/*******************************************************************
 Function: lock_graph_cst::convert_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysis_cst::convert_deadlocks(const namespacet &ns,
				    xmlt &dest)
{
  dest = xmlt("deadlock-analysis");
  for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
      d_it != potential_deadlocks.end(); ++d_it)
  {
    xmlt &d=dest.new_element("potential-deadlock");
    for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
	d_it != potential_deadlocks.end(); ++d_it)
    {
      for(lock_graph_cst::patht::const_iterator
	    p_it = d_it->begin(); p_it != d_it->end(); ++p_it)
      {
	lock_graph_cst::node_indext pn = graph.pred_node(*p_it);
	lock_graph_cst::node_indext sn = graph.succ_node(*p_it);
	if(p_it == d_it->begin())
	  graph.convert_node(ns,d,pn);
	graph.convert_edge(ns,d,pn,sn,*p_it);
	graph.convert_node(ns,d,sn);
      }
    }
  }
}

/*******************************************************************

 Function: lock_graph_analysis_cst::show_deadlocks

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void lock_graph_analysis_cst::show_deadlocks(const namespacet &ns,
		    ui_message_handlert::uit ui)
{
  switch (ui)
  {
  case ui_message_handlert::XML_UI:
  {
    xmlt xml;
    convert_deadlocks(ns,xml);
    std::cout << xml << std::endl;
  }
  break;

  case ui_message_handlert::PLAIN:
    output_statistics2(std::cout);
    output_deadlocks(ns,std::cout);
    break;

  default:
    ;
  }
}

/*******************************************************************

 Function: lock_graph_analysis_cst::output_statistics

 Inputs:

 Outputs:

 Purpose: after operator()

\*******************************************************************/

void lock_graph_analysis_cst::output_statistics1(std::ostream &out)
{
  out << "*** Statistics: " << std::endl;
  out << "  Number of threads:                "
      << statistics.threads.size() << std::endl;

  unsigned number_of_threads_in_loop = 0;
  for(const ai_cs_stackt &thread_id : statistics.threads)
  {
    if(!thread_id.frames.empty() &&
       is_in_loop(thread_id, std::get<1>(thread_id.frames.back())))
      number_of_threads_in_loop++;
  }
  out << "  Number of threads in loop:        "
      << number_of_threads_in_loop << std::endl;

  out << "  Number of locks:                  "
      << graph.size() << std::endl;
  out << "  Number of lock operations:        "
      << statistics.no_lock_operations << std::endl;
  out << "  Number of indeterminate lock ops: "
      << statistics.no_indet_lock_operations << std::endl;
  out << "  Size of largest lock set:         "
      << statistics.size_largest_lock_set << std::endl;

}
/*******************************************************************

 Function: lock_graph_analysis_cst::output_statistics

 Inputs:

 Outputs:

 Purpose: after detect_deadlocks()

\*******************************************************************/

void lock_graph_analysis_cst::output_statistics2(std::ostream &out)
{
  out << "  Number of cycles:                 "
      << statistics.no_cycles << std::endl;
  out << "  Number of non-concurrency checks: "
      << statistics.no_non_concurrent_checks << std::endl;

  std::size_t len_longest_valid_cycle = 0;
  for(deadlockst::const_iterator d_it = potential_deadlocks.begin();
      d_it != potential_deadlocks.end(); ++d_it)
    len_longest_valid_cycle = std::max(len_longest_valid_cycle,
				       d_it->size());
  out << "  Length of longest valid cycle:    "
      << len_longest_valid_cycle << std::endl;
}
