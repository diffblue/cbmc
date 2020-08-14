/// \file
/// \author Diffblue Ltd.
///
/// Provides a way to compute edit distance between two strings

#include "edit_distance.h"

levenshtein_automatont::levenshtein_automatont(
  const std::string &string,
  std::size_t allowed_errors)
{
  const std::size_t layer_offset = string.size() + 1;
  for(std::size_t i = 0; i <= allowed_errors; ++i)
  {
    final_states.push_back(string.size() + layer_offset * i);
  }
  for(std::size_t string_index = 0; string_index < string.size();
      ++string_index)
  {
    for(std::size_t error_layer = 0; error_layer <= allowed_errors;
        ++error_layer)
    {
      // position string_index matches
      nfa.add_transition(
        error_layer * layer_offset + string_index,
        string[string_index],
        error_layer * layer_offset + string_index + 1);
      if(error_layer < allowed_errors)
      {
        // insertion, swap or deletion
        nfa.add_arbitrary_transition(
          error_layer * layer_offset + string_index,
          (error_layer + 1) * layer_offset + string_index);
        nfa.add_epsilon_transition(
          error_layer * layer_offset + string_index,
          (error_layer + 1) * layer_offset + string_index + 1);
        nfa.add_arbitrary_transition(
          error_layer * layer_offset + string_index,
          (error_layer + 1) * layer_offset + string_index + 1);
      }
    }
  }
  for(std::size_t error_layer = 0; error_layer < allowed_errors; ++error_layer)
  {
    // arbitrary transitions between error layers
    nfa.add_arbitrary_transition(
      error_layer * layer_offset + string.size(),
      (error_layer + 1) * layer_offset + string.size());
  }
}

bool levenshtein_automatont::matches(const std::string &string) const
{
  return get_edit_distance(string).has_value();
}

optionalt<std::size_t>
levenshtein_automatont::get_edit_distance(const std::string &string) const
{
  auto current = nfa.initial_state(0);
  for(const auto c : string)
  {
    current = nfa.next_state(current, c);
  }
  for(std::size_t distance = 0; distance < final_states.size(); ++distance)
  {
    if(current.contains(final_states[distance]))
    {
      return distance;
    }
  }
  return nullopt;
}
