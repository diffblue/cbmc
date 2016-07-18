/*******************************************************************\

Module: Which-Threads Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#include <util/config.h>
#include <util/graph.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/i2string.h>
#include <util/std_expr.h>
#include <util/xml.h>
#include <util/std_code.h>

#include <algorithm>

#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include "which_threads.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif



/*******************************************************************\

Function: which_threads_internalt::which_threads_internalt

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

which_threads_internalt::which_threads_internalt(const goto_functionst &_goto_functions)
  : goto_functions(_goto_functions),
    nr_functions(0),
    nr_shared_functions(0),
    ratio_shared_functions(0),
    nr_instructions(0),
    nr_shared_instructions(0),
    ratio_shared_instructions(0),
    min_nr_of_instructions(0),
    med_nr_of_instructions(0),
    max_nr_of_instructions(0),
    min_depth(0),
    med_depth(0),
    max_depth(0),
    nr_thread_categories(0),
    nr_thread_creation_inside_loop(0)
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &body=f_it->second.body;
    add(f_it->first, body);
  }

  typedef graph<visited_nodet<irep_idt> > grapht;

  grapht graph;
  
  std::set<irep_idt> nodes;

  for(edgest::const_iterator 
	it=edges.begin(); 
      it!=edges.end(); 
      ++it)
  {
    nodes.insert(it->first.first);
    nodes.insert(it->first.second);
  }

  std::map<irep_idt, unsigned> node_map;

  for(std::set<irep_idt>::const_iterator
	it=nodes.begin();
      it!=nodes.end();
      ++it)
  {
    unsigned node=graph.add_node();

    node_map[*it]=node;
  }


  std::vector<unsigned> loops;

  // add call edges to graph
  for(edgest::const_iterator 
	it=edges.begin(); 
      it!=edges.end(); 
      ++it)
  {
    unsigned i=node_map[it->first.first];
    unsigned j=node_map[it->first.second];

    if(it->second.inside_loop)
    {
      loops.push_back(j);
    }

    graph.add_edge(i,j);

    graph.edge(i,j)=it->first.second;
  }

  // propagate being inside a loop
  for(unsigned i=0; i<graph.size(); ++i)
    graph[i].visited=false;

  for(unsigned i=0; i<loops.size(); ++i)
  {
    graph.visit_reachable(loops[i]);
  }

  for(edgest::iterator
	it=edges.begin();
      it!=edges.end();
      ++it)
  {
    const irep_idt &id=it->first.second;

    bool inside_loop=graph[node_map[id]].visited;

    it->second.inside_loop=inside_loop;

    if(it->second.thread)
    {


      thread_categoryt
	&cat=thread_categories[id];

      cat.k+=it->second.k;

      cat.inside_loop=cat.inside_loop || inside_loop;
    }
  }

  std::map<irep_idt, unsigned>::const_iterator 
    it=node_map.find(goto_functions.entry_point());

  assert(it!=node_map.end());
  
  unsigned initial_node=it->second;
  
  
  // compute shortest paths to thread creations
  for(thread_categoriest::iterator
	it=thread_categories.begin();
      it!=thread_categories.end();
      ++it)
  {

    grapht::patht path;

    graph.shortest_path(
      initial_node,
      node_map[it->first],
      path); 

    // subtract one to account for _start function
    it->second.depth=path.size() - 1;
  }
  
  // determine functions used
  for(thread_categoriest::iterator
	it=thread_categories.begin();
      it!=thread_categories.end();
      ++it)
  {
    thread_categoryt &cat=it->second;


    if(cat.inside_loop)
    {
      shared_functions.insert(it->first);

      ++nr_thread_creation_inside_loop;
    }

    // mark everything as unreachable
    for(unsigned i=0; i<graph.size(); ++i)
      graph[i].visited=false;

    // mark reachable nodes
    graph.visit_reachable(node_map[it->first]);

    // collect everything that was reached
    for(unsigned i=0; i<graph.size(); ++i)
    {
      if(graph[i].visited)
      {
        for(grapht::nodet::edgest::const_iterator
	      eit=graph[i].out.begin();
            eit!=graph[i].out.end();
            ++eit)
        {
          if(graph[eit->first].visited)
          {
            if(cat.used_functions.count(eit->second)==0)
            {
              cat.used_functions.insert(eit->second);
              cat.nr_instructions+=count_instructions(eit->second);
            }

            if(cat.inside_loop)
            {
              shared_functions.insert(eit->second);
            }
          }
        }
      }
    }

    thread_nr_instructions.push_back(cat.nr_instructions);
    thread_creation_depths.push_back(cat.depth);
  }

  nr_thread_categories=thread_categories.size();

  /* aggregate number of uses per function */
  for(thread_categoriest::iterator
	it=thread_categories.begin();
      it!=thread_categories.end();
      ++it)
  {
    const thread_categoryt::used_functionst 
      &used_functions=it->second.used_functions;

    for(thread_categoryt::used_functionst::const_iterator
	  uit=used_functions.begin();
        uit!=used_functions.end();
        ++uit)
    {
      ++use_counters[*uit];
    }


    ++use_counters[it->first];
  }

  for(use_counterst::const_iterator
	it=use_counters.begin();
      it!=use_counters.end();
      ++it)
  {
    if(it->second>1) {
      ++nr_shared_functions;

      nr_shared_instructions+=count_instructions(it->first);      

      shared_functions.insert(it->first);
    }
  }


  for(std::set<irep_idt>::const_iterator
	it=shared_functions.begin();
      it!=shared_functions.end();
      ++it)
  {
    add_to_target_set(*it, is_shared_set);
  }

  // TODO: modify this to exclude code before thread creation
  //   that's not that easy: we need a proper thread-sensitive
  //      static analysis that is able to determine when which 
  //      threads are running
  if(thread_categories.size()>0)
  {
    forall_goto_functions(f_it, goto_functions)
    {
      add_to_target_set(f_it->first, is_threaded_set);
    }
  }
  
  nr_functions=goto_functions.function_map.size();

  ratio_shared_functions=float(nr_shared_functions)/ nr_functions;

  ratio_shared_instructions=float(nr_shared_instructions)/nr_instructions;


  // compute extrema and medians of per-thread measures

  if(nr_thread_categories>0)  
  {
    std::sort(thread_nr_instructions.begin(), thread_nr_instructions.end());
    min_nr_of_instructions=thread_nr_instructions[0];
    med_nr_of_instructions=thread_nr_instructions[thread_nr_instructions.size()/2];
    max_nr_of_instructions=thread_nr_instructions.back();

    std::sort(thread_creation_depths.begin(), thread_creation_depths.end());
    min_depth=thread_creation_depths[0];
    med_depth=thread_creation_depths[thread_creation_depths.size()/2];
    max_depth=thread_creation_depths.back();
  }
}


/*******************************************************************\

Function: which_threads_internalt::add_to_is_threaded

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::add_to_target_set(
  const irep_idt &function,
  target_sett &is_threaded_set)
{
  // things inside thread
  goto_functionst::function_mapt::const_iterator fit=
    goto_functions.function_map.find(function);
 
  if(fit==goto_functions.function_map.end())
    return;
  
  forall_goto_program_instructions(i_it, (*fit).second.body)
  {
    const goto_programt::instructiont &instruction=*i_it;
  
    if(instruction.is_assign() || 
       instruction.is_goto() || 
       instruction.is_assume())
    {
      // must contain
      // - a shared variable
      // - a pointer
      // - a dirty variable (TODO)
      // - all control-flow dependencies must be included (TODO)
    
      is_threaded_set.insert(i_it);
    }
  }
}


/*******************************************************************\

Function: which_threads_internalt::count_instructions

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned which_threads_internalt::count_instructions(const irep_idt &name)
{
  unsigned result=0;

  goto_functionst::function_mapt::const_iterator
    fit=goto_functions.function_map.find(name);

  if(fit!=goto_functions.function_map.end())
  {
    forall_goto_program_instructions(i_it, (fit->second).body)
    {
      // count instructions
      ++result;
    }
  }

  return result;
}

/*******************************************************************\

Function: which_threads_internalt::add

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::add(
  const irep_idt &function,
  const goto_programt &body)
{
  // filter out CPROVER internal functions
  if(has_prefix(id2string(function), CPROVER_PREFIX))
    return;

  natural_loopst natural_loops;

  natural_loops(body);

  natural_loopst::natural_loopt loop_content;

  for (natural_loopst::loop_mapt::const_iterator 
         it= natural_loops.loop_map.begin();
       it!=natural_loops.loop_map.end();
       ++it)
  {

    const natural_loopst::natural_loopt &loop_body=it->second;

    loop_content.insert(loop_body.begin(), loop_body.end());
  }


  forall_goto_program_instructions(i_it, body)
  {
    // count instructions
    ++nr_instructions;

    if(i_it->is_function_call())
    {
      const code_function_callt &call=to_code_function_call(i_it->code);
      const exprt &function_expr=call.function();
      
      if(function_expr.id()!=ID_symbol)
      {
        continue;
      }

      const irep_idt &function_identifier=
        to_symbol_expr(function_expr).get_identifier();


      if(id2string(function_identifier)==config.ansi_c.create_thread)
      {
        const exprt::operandst &call_arguments=call.arguments();
        // expecting at least 3 arguments
        assert(call_arguments.size() > config.ansi_c.create_thread_arg_no_of_function);
      
        // function invoked by pthread_create is third call argument
        exprt 
          callee=call_arguments[config.ansi_c.create_thread_arg_no_of_function];
        
        symbol_exprt function_symbol(ID_nil);

        if(callee.id()==ID_typecast)
	  callee=callee.op0();

        if(callee.id()==ID_address_of)
        {
          if(callee.op0().id()==ID_symbol)
          {
            function_symbol=to_symbol_expr(callee.op0());
          }
        }

        if(function_symbol.is_not_nil())
        {
	  bool inside_loop=loop_content.count(i_it);

          edget thread_edge(true, function_symbol.get_identifier(), 1, inside_loop);

          add(std::make_pair(function, function_symbol.get_identifier()), thread_edge);
        }
      }
      else
      {
        const irep_idt &function_identifier=
          to_symbol_expr(function_expr).get_identifier();

        bool inside_loop=loop_content.count(i_it);

        edget call_edge(false, function_identifier, 1, inside_loop);
        
        add(std::make_pair(function, function_identifier), call_edge);
      }
    }
    else if(i_it->is_start_thread())
    {
      const goto_programt::instructiont &i=*i_it;

      if(i.targets.empty())
      {
      }
      else if(i.targets.size()==1)
      {
        const goto_programt::instructiont &target=*i.get_target();

        if(target.is_function_call())
        {
          const code_function_callt &call=to_code_function_call(target.code);
 
          const exprt &function_expr=call.function();

          if(function_expr.id()!=ID_symbol)
            continue;
  
          const irep_idt &function_identifier=
            to_symbol_expr(function_expr).get_identifier();

          bool inside_loop=loop_content.count(i_it);

          edget call_edge(true, function_identifier, 1, inside_loop);
      
          add(std::make_pair(function, function_identifier), call_edge);
        }
      } // if i.targets
    } // if is_start_thread
  } // forall
}


/*******************************************************************\

Function: which_threads_internalt::add

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::add(
  const caller_calleet &cc,
  const edget &edge)
{
  edgest::iterator it=edges.find(cc);

  if(it==edges.end())
  {
    edges.insert(std::make_pair(cc,edge));
  }
  else if(it!=edges.end())
  {
    edget &other_edge=it->second;

    if(!edge.thread && other_edge.thread)
    {
      // ignore
    }
    else
    {
      other_edge.k +=edge.k;
      other_edge.inside_loop=other_edge.inside_loop || edge.inside_loop;
    }
  }
}


/*******************************************************************\

Function: which_threads_internalt::output_dot

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::output_dot(std::ostream &out) const
{
  //TODO: add multiplicity information
  //TODO: add distinction between call edge and thread-creation edge

  out << "digraph call_edges {\n";
  out << "concentrate=true;\n";

  for(edgest::const_iterator it=edges.begin();
      it!=edges.end();
      it++)
  {
    const edget &edge=it->second;
  
    if(edge.thread)
    {
      std::string label="Thread creation";

      if(edge.inside_loop)
      {
        label+=": inside loop";
      }

      if(edge.k>1)
      {
        label+=", " + i2string(edge.k) + " occurrences";
      }


      out << "  \"" << it->first.first << "\" -> "
          << "\"" << it->first.second << "\" "
          << " [arrowhead=\"vee\",color=\"red\",label=\""
          << label << "\"];"
          << "\n";
    }
    else
    {
      out << "  \"" << it->first.first << "\" -> "
          << "\"" << it->first.second << "\" "
          << " [arrowhead=\"vee\"];"
          << "\n";
    }
  }
  
  for(use_counterst::const_iterator
	it=use_counters.begin();
      it!=use_counters.end();
      ++it)  
  {
    if(it->second>1)
      out << it->first << "[bgfill=\"yellow\"];\n";
  }


  out << "}\n";
}

/*******************************************************************\

Function: which_threads_internalt::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::output(std::ostream &out) const
{
  for(edgest::const_iterator
	it=edges.begin();
      it!=edges.end();
      it++)
  {
    const edget &edge=it->second;
  
    if(edge.thread)
    {
      out << it->first.first << " ="<< edge.k << (edge.inside_loop ? "*" : "") << "=> " << it->first.second << "\n";
    }
    else
    {
      out << it->first.first << " -"<< edge.k << (edge.inside_loop ? "*" : "") << "-> " << it->first.second << "\n";
    }
  
  }

  for(thread_categoriest::const_iterator
	it=thread_categories.begin();
      it!=thread_categories.end();
      ++it)
  {
    const thread_categoryt &cat=it->second;

    out << "Thread category " << it->first << "\n";

    out << "  Depth: " << cat.depth << "\n";
    out << "  Static creation sites: " << cat.k << "\n";
    out << "  Created in loop: " << cat.inside_loop << "\n";
    out << "  Nr of functions: " << cat.used_functions.size() << "\n";
    out << "  Nr of instructions: " << cat.nr_instructions << "\n";

    /*  
	out << "  ";

	for(std::set<irep_idt>::const_iterator
	fit=cat.used_functions.begin();
	fit!=cat.used_functions.end();
	++fit)
	{
	out << *fit << " ";
	}
    
	out << "\n";
    */
  }

  out << "Summarised statistics" << "\n";

  out << "  Nr of thread categories " << nr_thread_categories << "\n";
  out << "  Nr of thread creations inside loop " << nr_thread_creation_inside_loop << "\n";

  out << "  Mininum nr of instructions per thread " << min_nr_of_instructions << "\n";
  out << "  Median  nr of instructions per thread " << med_nr_of_instructions << "\n";
  out << "  Maximum nr of instructions per thread " << max_nr_of_instructions << "\n";

  out << "  Minimum thread creation depth " << min_depth << "\n";
  out << "  Median  thread creation depth " << med_depth << "\n";
  out << "  Maximum thread creation depth " << max_depth << "\n";

  out << "  Nr of instructions " << nr_instructions << "\n";
  out << "  Nr of shared instructions " << nr_shared_instructions << "\n";
  out << "  Ratio Shared instructions " << ratio_shared_instructions << "\n";

  out << "  Nr of Functions " << nr_functions << "\n";
  out << "  Nr of Shared functions " << nr_shared_functions << "\n";
  out << "  Ratio Shared Functions " << ratio_shared_functions << "\n";
}

/*******************************************************************\

Function: which_threads_internalt::output_xml

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void which_threads_internalt::output_xml(std::ostream &out) const
{
  //TODO: add multiplicity information

  for(edgest::const_iterator
	it=edges.begin();
      it!=edges.end();
      it++)
  {
    const edget &edge=it->second;
 
    if(edge.thread)
    {
      out << "<thread_edge caller=\"";
      xmlt::escape_attribute(id2string(it->first.first), out);
      out << "\" callee=\"";
      xmlt::escape_attribute(id2string(it->first.second), out);
      out << "\">\n";    
    }
    else
    {
      out << "<call_edge caller=\"";
      xmlt::escape_attribute(id2string(it->first.first), out);
      out << "\" callee=\"";
      xmlt::escape_attribute(id2string(it->first.second), out);
      out << "\">\n";
    }
  }
}
