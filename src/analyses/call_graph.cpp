/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graph

#include "call_graph.h"

#include <util/std_expr.h>
#include <util/xml.h>

call_grapht::call_grapht()
{
}

call_grapht::call_grapht(const goto_modelt &goto_model)
{
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    const goto_programt &body=f_it->second.body;
    add(f_it->first, body);
  }
}

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
        add(function, to_symbol_expr(function_expr).get_identifier());
    }
  }
}

void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee)
{
  std::size_t caller_idx = node_numbering.number(caller);
  if(caller_idx >= nodes.size())
  {
    node_indext node_index = add_node();
    nodes[node_index].function_name = caller;
  }

  std::size_t callee_idx = node_numbering.number(callee);
  if(callee_idx >= nodes.size())
  {
    node_indext node_index = add_node();
    nodes[node_index].function_name = callee;
  }

  add_edge(caller_idx, callee_idx);
}


void call_grapht::output_dot_node(std::ostream &out, node_indext n) const
{
  const nodet &node = nodes.at(n);

  for(const auto &edge : node.out)
  {
    out << "  \"" << node.function_name << "\" -> " << "\""
        << nodes[edge.first].function_name << "\" " << " [arrowhead=\"vee\"];"
        << "\n";
  }
}

void call_grapht::output_xml_node(std::ostream &out, node_indext n) const
{
  const nodet &node = nodes.at(n);

  for(const auto &edge : node.out)
  {
    out << "<call_graph_edge caller=\"";
    xmlt::escape_attribute(id2string(node.function_name), out);
    out << "\" callee=\"";
    xmlt::escape_attribute(id2string(nodes[edge.first].function_name), out);
    out << "\">\n";
  }
}

void call_grapht::output_xml(std::ostream &out) const
{
  for(node_indext n = 0; n < nodes.size(); n++)
    output_xml_node(out, n);
}

call_grapht call_grapht::get_inverted() const
{
  call_grapht result;
  for(const auto &n : nodes)
  {
    for(const auto &i : n.in)
      result.add(n.function_name, nodes[i.first].function_name);
  }
  return result;
}

std::unordered_set<irep_idt, irep_id_hash>
call_grapht::reachable_functions(irep_idt start_function)
{
  std::unordered_set<irep_idt, irep_id_hash> result;
  std::list<node_indext> worklist;
  node_indext start_index;

  if(get_node_index(start_function, start_index))
    worklist.push_back(start_index);
  else
    throw "no start function found in call graph";

  while(!worklist.empty())
  {
    const node_indext id = worklist.front();
    worklist.pop_front();

    result.insert(nodes[id].function_name);
    for(const auto &o : nodes[id].out)
    {
      if(result.find(nodes[o.first].function_name) == result.end())
        worklist.push_back(o.first);
    }
  }

  return result;
}
