/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graphs

#include "call_graph.h"

#include <util/std_expr.h>
#include <util/xml.h>

call_grapht::call_grapht(bool collect_callsites):
  collect_callsites(collect_callsites)
{
}

call_grapht::call_grapht(const goto_modelt &goto_model, bool collect_callsites):
  call_grapht(goto_model.goto_functions, collect_callsites)
{
}

call_grapht::call_grapht(
  const goto_functionst &goto_functions, bool collect_callsites):
  collect_callsites(collect_callsites)
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
      {
        const irep_idt &callee=to_symbol_expr(function_expr).get_identifier();
        add(function, callee);
        if(collect_callsites)
          callsites[{function, callee}].insert(i_it);
      }
    }
  }
}

void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee)
{
  graph.insert(std::pair<irep_idt, irep_idt>(caller, callee));
}

/// Add edge with optional callsite information
/// \param caller: caller function
/// \param callee: callee function
/// \param callsite: call instruction responsible for this edge. Note this is
///   only stored if `collect_callsites` was specified during construction.
void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee,
  locationt callsite)
{
  add(caller, callee);
  if(collect_callsites)
    callsites[{caller, callee}].insert(callsite);
}

/// Returns an inverted copy of this call graph
/// \return Inverted (callee -> caller) call graph
call_grapht call_grapht::get_inverted() const
{
  call_grapht result;
  for(const auto &caller_callee : graph)
    result.add(caller_callee.second, caller_callee.first);
  return result;
}

std::string call_grapht::format_callsites(const edget &edge) const
{
  PRECONDITION(collect_callsites);
  std::string ret="{";
  for(const locationt &loc : callsites.at(edge))
  {
    if(ret.size()>1)
      ret+=", ";
    ret+=std::to_string(loc->location_number);
  }
  ret+='}';
  return ret;
}

void call_grapht::output_dot(std::ostream &out) const
{
  out << "digraph call_graph {\n";

  for(const auto &edge : graph)
  {
    out << "  \"" << edge.first << "\" -> "
        << "\"" << edge.second << "\" "
        << " [arrowhead=\"vee\"";
    if(collect_callsites)
      out << " label=\"" << format_callsites(edge) << "\"";
    out << "];\n";
  }

  out << "}\n";
}

void call_grapht::output(std::ostream &out) const
{
  for(const auto &edge : graph)
  {
    out << edge.first << " -> " << edge.second << "\n";
    if(collect_callsites)
      out << "  (callsites: " << format_callsites(edge) << ")\n";
  }
}

void call_grapht::output_xml(std::ostream &out) const
{
  // Note I don't implement callsite output here; I'll leave that
  // to the first interested XML user.
  if(collect_callsites)
    out << "<!-- XML call-graph representation does not document callsites yet."
      " If you need this, edit call_grapht::output_xml -->\n";
  for(const auto &edge : graph)
  {
    out << "<call_graph_edge caller=\"";
    xmlt::escape_attribute(id2string(edge.first), out);
    out << "\" callee=\"";
    xmlt::escape_attribute(id2string(edge.second), out);
    out << "\">\n";
  }
}
