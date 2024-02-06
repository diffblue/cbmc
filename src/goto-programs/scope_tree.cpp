/*******************************************************************\

 Module: Scope Tree

 Author: John Dumbell, john.dumbell@diffblue.com

\*******************************************************************/

#include "scope_tree.h"

void scope_treet::add(
  const codet &destructor,
  std::optional<goto_programt::targett> declaration)
{
  auto previous_node = get_current_node();
  using declaration_optt = std::optional<declaration_statet>;
  auto declaration_opt =
    declaration ? declaration_optt{{*declaration}} : declaration_optt{};
  auto new_node = scope_graph.add_node(destructor, std::move(declaration_opt));
  scope_graph.add_edge(previous_node, new_node);
  current_node = new_node;
}

std::optional<codet> &scope_treet::get_destructor(node_indext index)
{
  PRECONDITION(index < scope_graph.size());
  return scope_graph[index].destructor_value;
}

std::optional<scope_treet::declaration_statet> &
scope_treet::get_declaration(node_indext index)
{
  PRECONDITION(index < scope_graph.size());
  return scope_graph[index].declaration;
}

const ancestry_resultt scope_treet::get_nearest_common_ancestor_info(
  node_indext left_index,
  node_indext right_index)
{
  std::size_t left_unique_count = 0, right_unique_count = 0;
  while(right_index != left_index)
  {
    if(right_index > left_index)
    {
      auto edge_map = scope_graph[right_index].in;
      INVARIANT(
        !edge_map.empty(),
        "Node at index " + std::to_string(right_index) +
          " has no parent, can't find an ancestor.");
      right_index = edge_map.begin()->first, right_unique_count++;
    }
    else
    {
      auto edge_map = scope_graph[left_index].in;
      INVARIANT(
        !edge_map.empty(),
        "Node at index " + std::to_string(left_index) +
          " has no parent, can't find an ancestor.");
      left_index = edge_map.begin()->first, left_unique_count++;
    }
  }

  // At this point it doesn't matter which index we return as both are the same.
  return {right_index, left_unique_count, right_unique_count};
}

const std::vector<destructor_and_idt> scope_treet::get_destructors(
  std::optional<node_indext> end_index,
  std::optional<node_indext> starting_index)
{
  node_indext next_id = starting_index.value_or(get_current_node());
  node_indext end_id = end_index.value_or(0);

  std::vector<destructor_and_idt> codes;
  while(next_id > end_id)
  {
    auto node = scope_graph[next_id];
    auto &destructor = node.destructor_value;
    if(destructor)
      codes.emplace_back(destructor_and_idt(*destructor, next_id));

    next_id = node.in.begin()->first;
  }

  return codes;
}

void scope_treet::set_current_node(std::optional<node_indext> val)
{
  if(val)
    set_current_node(*val);
}

void scope_treet::set_current_node(node_indext val)
{
  current_node = val;
}

void scope_treet::descend_tree()
{
  node_indext current_node = get_current_node();
  if(current_node != 0)
  {
    set_current_node(scope_graph[current_node].in.begin()->first);
  }
}

node_indext scope_treet::get_current_node() const
{
  return current_node;
}

scope_treet::scope_nodet::scope_nodet(
  codet destructor,
  std::optional<declaration_statet> declaration)
  : destructor_value(std::move(destructor)), declaration(std::move(declaration))
{
}
