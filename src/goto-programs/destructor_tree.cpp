/*******************************************************************\

 Module: Destructor Tree

 Author: John Dumbell, john.dumbell@diffblue.com

\*******************************************************************/

#include "destructor_tree.h"

void destructor_treet::add(const codet &destructor)
{
  auto previous_node = get_current_node();
  auto new_node = destruction_graph.add_node(destructor);
  destruction_graph.add_edge(previous_node, new_node);
  current_node = new_node;
}

optionalt<codet> &destructor_treet::get_destructor(node_indext index)
{
  PRECONDITION(index < destruction_graph.size());
  return destruction_graph[index].destructor_value;
}

const ancestry_resultt destructor_treet::get_nearest_common_ancestor_info(
  node_indext left_index,
  node_indext right_index)
{
  std::size_t left_unique_count = 0, right_unique_count = 0;
  while(right_index != left_index)
  {
    if(right_index > left_index)
    {
      auto edge_map = destruction_graph[right_index].in;
      INVARIANT(
        !edge_map.empty(),
        "Node at index " + std::to_string(right_index) +
          " has no parent, can't find an ancestor.");
      right_index = edge_map.begin()->first, right_unique_count++;
    }
    else
    {
      auto edge_map = destruction_graph[left_index].in;
      INVARIANT(
        !edge_map.empty(),
        "Node at index " + std::to_string(left_index) +
          " has no parent, can't find an ancestor.");
      left_index = edge_map.begin()->first, left_unique_count++;
    }
  }

  // At this point it dosen't matter which index we return as both are the same.
  return {right_index, left_unique_count, right_unique_count};
}

const std::vector<destructor_and_idt> destructor_treet::get_destructors(
  optionalt<node_indext> end_index,
  optionalt<node_indext> starting_index)
{
  node_indext next_id = starting_index.value_or(get_current_node());
  node_indext end_id = end_index.value_or(0);

  std::vector<destructor_and_idt> codes;
  while(next_id > end_id)
  {
    auto node = destruction_graph[next_id];
    auto &destructor = node.destructor_value;
    if(destructor)
      codes.emplace_back(destructor_and_idt(*destructor, next_id));

    next_id = node.in.begin()->first;
  }

  return codes;
}

void destructor_treet::set_current_node(optionalt<node_indext> val)
{
  if(val)
    set_current_node(*val);
}

void destructor_treet::set_current_node(node_indext val)
{
  current_node = val;
}

void destructor_treet::descend_tree()
{
  node_indext current_node = get_current_node();
  if(current_node != 0)
  {
    set_current_node(destruction_graph[current_node].in.begin()->first);
  }
}

node_indext destructor_treet::get_current_node() const
{
  return current_node;
}
