/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graph

#ifndef CPROVER_ANALYSES_CALL_GRAPH_H
#define CPROVER_ANALYSES_CALL_GRAPH_H

#include <iosfwd>
#include <map>
#include <unordered_set>

#include <goto-programs/goto_model.h>

#include <util/irep.h>
#include <util/graph.h>
#include <util/numbering.h>


/// Function call graph inherits from grapht to allow forward and
/// backward traversal of the function call graph

struct call_graph_nodet: public graph_nodet<empty_edget>
{
  typedef graph_nodet<empty_edget>::edget edget;
  typedef graph_nodet<empty_edget>::edgest edgest;

  irep_idt function_name;
  bool visited = false;
};

class call_grapht: public grapht<call_graph_nodet>
{
public:
  call_grapht();
  explicit call_grapht(const goto_modelt &);

  void add(const irep_idt &caller, const irep_idt &callee);
  void output_xml(std::ostream &out) const;
  call_grapht get_inverted() const;
  std::unordered_set<irep_idt, irep_id_hash>
      reachable_functions(irep_idt start);
  std::list<irep_idt>shortest_function_path(irep_idt src, irep_idt dest);

  bool get_node_index(const irep_idt& function_name, node_indext &n) const
  {
    for(node_indext idx = 0; idx < nodes.size(); idx++)
    {
      if(nodes[idx].function_name == function_name)
      {
        n = idx;
        return true;
      }
    }
    return false;
  }

  std::unordered_set<irep_idt, irep_id_hash> get_successors(
      const irep_idt& function_name) const
  {
    std::unordered_set<irep_idt, irep_id_hash> result;
    node_indext function_idx;
    if(!get_node_index(function_name, function_idx))
      return result;

    for(const auto &o : nodes[function_idx].out)
      result.insert(nodes[o.first].function_name);
    return result;
  }


protected:
  void output_dot_node(std::ostream &out, node_indext n) const override;
  void output_xml_node(std::ostream &out, node_indext n) const;
  numbering<irep_idt> node_numbering;
  void add(const irep_idt &function,
           const goto_programt &body);
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
