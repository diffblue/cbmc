/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graphs

#include <util/std_expr.h>
#include <util/xml.h>

#include "call_graph.h"

void call_grapht::operator()()
{
  forall_goto_functions(f_it, goto_functions)
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
  graph.insert(std::pair<irep_idt, irep_idt>(caller, callee));
}

void call_grapht::compute_reachable(
  const irep_idt entry_point,
  std::unordered_set<irep_idt, irep_id_hash> &reachable_functions)
{
  assert(reachable_functions.empty());
  std::list<irep_idt> worklist;
  const goto_functionst::function_mapt::const_iterator e_it=
    goto_functions.function_map.find(entry_point);
  assert(e_it!=goto_functions.function_map.end());
  worklist.push_back(entry_point);
  do
  {
    const irep_idt id=worklist.front();
    worklist.pop_front();

    reachable_functions.insert(id);

    const auto &p=graph.equal_range(id);

    for(auto it=p.first; it!=p.second; it++)
    {
      const irep_idt callee=it->second;

      if(reachable_functions.find(callee)==reachable_functions.end())
        worklist.push_back(callee);
    }
  }
  while(!worklist.empty());
}
void call_grapht::output_dot(std::ostream &out) const
{
  out << "digraph call_graph {\n";

  for(const auto &edge : graph)
  {
    out << "  \"" << edge.first << "\" -> "
        << "\"" << edge.second << "\" "
        << " [arrowhead=\"vee\"];"
        << "\n";
  }

  out << "}\n";
}

void call_grapht::output(std::ostream &out) const
{
  for(const auto &edge : graph)
  {
    out << edge.first << " -> " << edge.second << "\n";
  }
}

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
