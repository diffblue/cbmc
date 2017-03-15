/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "call_graph.h"
#include <util/std_expr.h>
#include <util/xml.h>
#include <algorithm>
#include <iterator>


/*******************************************************************\

Function: call_grapht::call_grapht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

call_grapht::call_grapht()
{
}

/*******************************************************************\

Function: call_grapht::call_grapht

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

call_grapht::call_grapht(const goto_functionst &goto_functions)
{
  forall_goto_functions(f_it, goto_functions)
  {
    const goto_programt &body=f_it->second.body;
    add(f_it->first, body);
  }
}

/*******************************************************************\

Function: call_grapht::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::add(
  const irep_idt &function,
  const goto_programt &body)
{
  forall_goto_program_instructions(i_it, body)
  {
    if(i_it->is_function_call())
    {
      const exprt &function_expr=to_code_function_call(i_it->code).function();
      if(function_expr.id()==ID_symbol)
        add(function, to_symbol_expr(function_expr).get_identifier(), {i_it});
    }
  }
}

void call_grapht::swap(call_grapht &other)
{
  std::swap(graph, other.graph);
  std::swap(map_from_edges_to_call_locations,
            other.map_from_edges_to_call_locations);
}


/*******************************************************************\

Function: call_grapht::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee)
{
  graph.insert(std::pair<irep_idt, irep_idt>(caller, callee));
}

void call_grapht::add(const irep_idt &caller, const irep_idt &callee,
  const map_from_edges_to_call_locationst::mapped_type &call_sites)
{
  bool exists=false;
  const call_grapht::call_edges_ranget range=out_edges(caller);
  for(auto it=range.first; it!=range.second; ++it)
    if(it->second==callee)
    {
      exists=true;
      break;
    }
  if(!exists)
    add(caller, callee);
  std::copy(
    call_sites.cbegin(), call_sites.cend(),
    std::back_inserter(map_from_edges_to_call_locations[{caller, callee}]));
}


/*******************************************************************\

Function: call_grapht::output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::output_dot(std::ostream &out) const
{
  out << "digraph call_graph {\n"
      << "  node [fontsize=12 shape=box];\n";
  for(const auto &edge : graph)
  {
    out << "  \"" << edge.first << "\" -> "
        << "\"" << edge.second << "\" "
        << " [label=\"{";
    bool first=true;
    for(const auto instr_it :
        get_map_from_edges_to_call_locations().at({edge.first, edge.second}))
    {
      if(!first)
        out << ",";
      out << instr_it->location_number;
      first=false;
    }
    out << "}\"];\n";
  }
  out << "}\n";
}


/*******************************************************************\

Function: call_grapht::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::output(std::ostream &out) const
{
  for(const auto &edge : graph)
  {
    out << edge.first << " -> " << edge.second << "\n";
  }
}

/*******************************************************************\

Function: call_grapht::output_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void call_grapht::output_xml(std::ostream &out) const
{
  for(const auto &edge : graph)
  {
    out << "<call_graph_edge caller=\"";
    xmlt::escape_attribute(id2string(edge.first), out);
    out << "\" callee=\"";
    xmlt::escape_attribute(id2string(edge.second), out);
    out << "\">\n";
  }
}

/*******************************************************************\

Function: call_grapht::out_edges

  Inputs: `caller`: node to search for

 Outputs: Returns list of edges whose first component is `caller`.

 Purpose:

\*******************************************************************/

call_grapht::call_edges_ranget
call_grapht::out_edges(const irep_idt &caller) const
{
  return graph.equal_range(caller);
}

/*******************************************************************\

Function: inverted_partial_topological_order

  Inputs: `call_graph`: Call graph
          `start_function`: start node, must occur in call graph
          `processed_functions`: set of functions already seen

 Outputs: `output`: inverted topological sort of the graph reachable
            from start node (i.e. leaves first, root last)
          `processed_functions`: set of functions already seen

 Purpose: Get reverse-top-sorted subgraph

\*******************************************************************/

void inverted_partial_topological_order(
  const call_grapht &call_graph,
  const irep_idt &start_function,
  std::unordered_set<irep_idt, dstring_hash> &processed_functions,
  std::vector<irep_idt> &output)
{
  if(processed_functions.count(start_function)!=0ULL)
    return;
  processed_functions.insert(start_function);
  const call_grapht::call_edges_ranget range =
    call_graph.out_edges(start_function);
  for(auto it=range.first; it!=range.second; ++it)
    inverted_partial_topological_order(
      call_graph,
      it->second,
      processed_functions,
      output);
  output.push_back(start_function);
}

/*******************************************************************\

Function: get_inverted_topological_order

  Inputs: `call_graph`: Call graph
          `functions`: map containing all functions of interest;
            only function names are used to index into call graph;
            function bodies are ignored.

 Outputs: `output`: inverted topological sort of the graph reachable
            from start node (i.e. leaves first, root last)

 Purpose: Get reverse-top-sorted call graph

\*******************************************************************/

void get_inverted_topological_order(
  const call_grapht& call_graph,
  const goto_functionst& functions,
  std::vector<irep_idt>& output)
{
  std::unordered_set<irep_idt, dstring_hash> processed;
  for(const auto &elem : functions.function_map)
    inverted_partial_topological_order(
      call_graph,
      elem.first,
      processed,
      output);
}

/*******************************************************************\

Function: exists_direct_call

  Inputs: `call_graph`: Call graph
          `caller`: Caller
          `callee`: Potential callee

 Outputs: Returns true if call graph says caller calls callee.

 Purpose: See output

\*******************************************************************/


bool exists_direct_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee)
{
  const call_grapht::call_edges_ranget range =
    call_graph.out_edges(caller);
  for(auto it=range.first; it!=range.second; ++it)
    if(callee==it->second)
      return true;
  return false;
}

/*******************************************************************\

Function: exists_direct_or_indirect_call

  Inputs: `call_graph`: Call graph
          `caller`: Caller
          `callee`: Potential callee
          `ignored_functions`: Functions to exclude from call graph
            for the purposes of finding a path

 Outputs: Returns true if call graph says caller can reach callee
          via any intermediate sequence of callees not occurring
          in ignored_functions

 Purpose: See output

\*******************************************************************/

bool exists_direct_or_indirect_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee,
  std::unordered_set<irep_idt, dstring_hash> &ignored_functions)
{
  if(ignored_functions.count(caller)!=0UL)
    return false;
  ignored_functions.insert(caller);
  if(exists_direct_call(call_graph, caller, callee))
    return ignored_functions.count(callee)==0UL;
  const call_grapht::call_edges_ranget range=
    call_graph.out_edges(caller);
  for(auto it=range.first; it!=range.second; ++it)
    if(exists_direct_or_indirect_call(
         call_graph,
         it->second,
         callee,
         ignored_functions))
      return true;
  return false;
}

/*******************************************************************\

Function: exists_direct_or_indirect_call

  Inputs: `call_graph`: Call graph
          `caller`: Caller
          `callee`: Potential callee

 Outputs: Returns true if call graph says caller can reach callee
          via any intermediate sequence of callees

 Purpose: See output

\*******************************************************************/

bool exists_direct_or_indirect_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee)
{
  std::unordered_set<irep_idt, dstring_hash>  ignored;
  return exists_direct_or_indirect_call(call_graph, caller, callee, ignored);
}

/*******************************************************************\

Function: computed_inverted_call_graph

  Inputs: `original_call_graph`: call graph

 Outputs: `output_inverted_call_graph`: input call graph with caller->
   callee edges reversed.

 Purpose: See output

\*******************************************************************/

void compute_inverted_call_graph(
  const call_grapht &original_call_graph,
  call_grapht &output_inverted_call_graph)
{
  assert(output_inverted_call_graph.graph.empty());
  for(const auto &elem : original_call_graph.graph)
    output_inverted_call_graph.add(
      elem.second, elem.first,
      original_call_graph.get_map_from_edges_to_call_locations().at(
        {elem.first, elem.second}));
}

/*******************************************************************\

Function: find_leaves_below_function

  Inputs: `call_graph`: call graph
          `function`: start node
          `to_avoid`: functions already visited

 Outputs: `output`: set of leaves reachable from 'function'
          `to_avoid`: functions already visited (with 'function'
            added)

 Purpose: See output

\*******************************************************************/


void find_leaves_below_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &to_avoid,
  std::unordered_set<irep_idt, dstring_hash> &output)
{
  if(to_avoid.count(function)!=0UL)
    return;
  to_avoid.insert(function);
  const call_grapht::call_edges_ranget range =
    call_graph.out_edges(function);
  if(range.first==range.second)
    output.insert(function);
  else
  {
    for(auto it=range.first; it!=range.second; ++it)
      find_leaves_below_function(call_graph, it->second, to_avoid, output);
  }
}

/*******************************************************************\

Function: find_leaves_below_function

  Inputs: `call_graph`: call graph
          `function`: start node

 Outputs: `output`: set of leaves reachable from 'function'

 Purpose: See output

\*******************************************************************/

void find_leaves_below_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &output)
{
  std::unordered_set<irep_idt, dstring_hash> to_avoid;
  find_leaves_below_function(call_graph, function, to_avoid, output);
}

void find_direct_or_indirect_callees_of_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &output)
{
  std::unordered_set<irep_idt, dstring_hash> leaves;
  find_leaves_below_function(call_graph, function, output, leaves);
  output.insert(leaves.cbegin(), leaves.cend());
}

void find_nearest_common_callees(
  const call_grapht &call_graph,
  const std::set<irep_idt> &functions,
  std::set<irep_idt> &output)
{
  if(functions.empty())
    return;
  if(functions.size()==1UL)
  {
    output.insert(*functions.cbegin());
    return;
  }

  std::map<irep_idt, std::size_t> counting;
  for(const auto &elem : call_graph.graph)
  {
    counting[elem.first]=0U;
    counting[elem.second]=0U;
  }
  for(const auto &fn : functions)
  {
    std::unordered_set<irep_idt, dstring_hash> callees;
    find_direct_or_indirect_callees_of_function(call_graph, fn, callees);
    assert(callees.count(fn)==1U);
    for(const auto &callee : callees)
      ++counting[callee];
  }

  std::set<irep_idt> leaves;
  for(const auto &elem : counting)
    if(elem.second!=0U)
    {
      const call_grapht::call_edges_ranget range=
        call_graph.out_edges(elem.first);
      if(range.first==range.second)
        leaves.insert(elem.first);
    }

  for(auto &elem : counting)
    if(leaves.count(elem.first)!=0UL)
      output.insert(elem.first);
    else if(elem.second!=0U && elem.second<functions.size())
    {
      const call_grapht::call_edges_ranget range=
        call_graph.out_edges(elem.first);
      for(auto it=range.first; it!=range.second; ++it)
      {
        auto cit=counting.find(it->second);
        if(cit->second==functions.size())
          output.insert(cit->first);
      }
    }
}
