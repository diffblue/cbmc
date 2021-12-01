/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graphs

#include "call_graph.h"

#include <util/xml.h>

#include <goto-programs/goto_model.h>

/// Create empty call graph
/// \param collect_callsites: if true, then each added graph edge will have
///   the calling instruction recorded in `callsites` map.
call_grapht::call_grapht(bool collect_callsites):
  collect_callsites(collect_callsites)
{
}

/// Create complete call graph
/// \param goto_model: model to search for callsites
/// \param collect_callsites: if true, then each added graph edge will have
///   the calling instruction recorded in `callsites` map.
call_grapht::call_grapht(const goto_modelt &goto_model, bool collect_callsites):
  call_grapht(goto_model.goto_functions, collect_callsites)
{
}

/// Create complete call graph
/// \param goto_functions: functions to search for callsites
/// \param collect_callsites: if true, then each added graph edge will have
///   the calling instruction recorded in `callsites` map.
call_grapht::call_grapht(
  const goto_functionst &goto_functions, bool collect_callsites):
  collect_callsites(collect_callsites)
{
  for(const auto &gf_entry : goto_functions.function_map)
  {
    const irep_idt &function_name = gf_entry.first;
    const goto_programt &body = gf_entry.second.body;
    nodes.insert(function_name);
    add(function_name, body);
  }
}

static void forall_callsites(
  const goto_programt &body,
  std::function<void(goto_programt::const_targett, const irep_idt &)> call_task)
{
  forall_goto_program_instructions(i_it, body)
  {
    if(i_it->is_function_call())
    {
      const exprt &function_expr = i_it->call_function();
      PRECONDITION_WITH_DIAGNOSTICS(
        function_expr.id() == ID_symbol,
        "call graph computation requires function pointer removal");
      const irep_idt &callee = to_symbol_expr(function_expr).get_identifier();
      call_task(i_it, callee);
    }
  }
}

/// Create call graph restricted to functions reachable from `root`
/// \param goto_functions: functions to search for callsites
/// \param root: function to start exploring the graph
/// \param collect_callsites: if true, then each added graph edge will have
///   the calling instruction recorded in `callsites` map.
call_grapht::call_grapht(
  const goto_functionst &goto_functions,
  const irep_idt &root,
  bool collect_callsites):
  collect_callsites(collect_callsites)
{
  std::stack<irep_idt, std::vector<irep_idt>> pending_stack;
  pending_stack.push(root);

  while(!pending_stack.empty())
  {
    irep_idt function=pending_stack.top();
    pending_stack.pop();

    nodes.insert(function);

    // if function is not in function_map, assume function has no body
    const auto &it = goto_functions.function_map.find(function);
    if(it == goto_functions.function_map.end())
      continue;

    const goto_programt &goto_program = it->second.body;

    forall_callsites(
      goto_program,
      [&](goto_programt::const_targett i_it, const irep_idt &callee)
      {
        add(function, callee, i_it);
        if(edges.find(callee)==edges.end())
          pending_stack.push(callee);
      }
    ); // NOLINT
  }
}

/// Create call graph restricted to functions reachable from `root`
/// \param goto_model: model to search for callsites
/// \param root: function to start exploring the graph
/// \param collect_callsites: if true, then each added graph edge will have
///   the calling instruction recorded in `callsites` map.
call_grapht::call_grapht(
  const goto_modelt &goto_model,
  const irep_idt &root,
  bool collect_callsites):
  call_grapht(goto_model.goto_functions, root, collect_callsites)
{
}

void call_grapht::add(
  const irep_idt &function,
  const goto_programt &body)
{
  forall_callsites(
    body,
    [&](goto_programt::const_targett i_it, const irep_idt &callee)
    {
      add(function, callee, i_it);
    }
  ); // NOLINT
}

/// Add edge
/// \param caller: caller function
/// \param callee: callee function
void call_grapht::add(
  const irep_idt &caller,
  const irep_idt &callee)
{
  edges.insert({caller, callee});
  nodes.insert(caller);
  nodes.insert(callee);
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
  result.nodes = nodes;
  for(const auto &caller_callee : edges)
    result.add(caller_callee.second, caller_callee.first);
  return result;
}

/// Helper class that maintains a map from function name to grapht node index
/// and adds nodes to the graph on demand.
class function_indicest
{
  typedef call_grapht::directed_grapht::node_indext node_indext;
  call_grapht::directed_grapht &graph;

public:
  std::unordered_map<irep_idt, node_indext> function_indices;

  explicit function_indicest(call_grapht::directed_grapht &graph):
    graph(graph)
  {
  }

  node_indext operator[](const irep_idt &function)
  {
    auto findit=function_indices.insert({function, 0});
    if(findit.second)
    {
      node_indext new_index=graph.add_node();
      findit.first->second=new_index;
      graph[new_index].function=function;
    }
    return findit.first->second;
  }
};

/// Returns a `grapht` representation of this call graph, suitable for use
/// with generic grapht algorithms. Note that parallel edges in call_grapht
/// (e.g. A { B(); B(); } appearing as two A->B edges) will be condensed in
/// the grapht output, so only one edge will appear. If `collect_callsites`
/// was set when this call-graph was constructed the edge will be annotated
/// with the call-site set.
/// \return grapht representation of this call_grapht
call_grapht::directed_grapht call_grapht::get_directed_graph() const
{
  call_grapht::directed_grapht ret;
  function_indicest function_indices(ret);

  // To make sure we include unreachable functions we first create indices
  // for all nodes in the graph
  for(const irep_idt &function_name : nodes)
    function_indices[function_name];

  for(const auto &edge : edges)
  {
    auto a_index=function_indices[edge.first];
    auto b_index=function_indices[edge.second];
    // Check then create the edge like this to avoid copying the callsites
    // set once per parallel edge, which could be costly if there are many.
    if(!ret.has_edge(a_index, b_index))
    {
      ret.add_edge(a_index, b_index);
      if(collect_callsites)
        ret[a_index].out[b_index].callsites=callsites.at(edge);
    }
  }

  ret.nodes_by_name=std::move(function_indices.function_indices);
  return ret;
}

/// Prints callsites responsible for a graph edge as comma-separated
/// location numbers, e.g. "{1, 2, 3}".
/// \param edge: graph edge
/// \return pretty representation of edge callsites
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

  for(const auto &edge : edges)
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
  for(const auto &edge : edges)
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
  for(const auto &edge : edges)
  {
    out << "<call_graph_edge caller=\"";
    xmlt::escape_attribute(id2string(edge.first), out);
    out << "\" callee=\"";
    xmlt::escape_attribute(id2string(edge.second), out);
    out << "\">\n";
  }
}

optionalt<std::size_t> call_grapht::directed_grapht::get_node_index(
  const irep_idt &function) const
{
  auto findit=nodes_by_name.find(function);
  if(findit==nodes_by_name.end())
    return optionalt<node_indext>();
  else
    return findit->second;
}
