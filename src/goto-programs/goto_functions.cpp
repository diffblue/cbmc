/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#include "goto_functions.h"

#include <algorithm>

void goto_functionst::compute_location_numbers()
{
  unused_location_number = 0;
  for(auto &func : function_map)
  {
    // Side-effect: bumps unused_location_number.
    func.second.body.compute_location_numbers(unused_location_number);
  }
}

void goto_functionst::compute_location_numbers(
  goto_programt &program)
{
  // Renumber just this single function. Use fresh numbers in case it has
  // grown since it was last numbered.
  program.compute_location_numbers(unused_location_number);
}

void goto_functionst::compute_incoming_edges()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_incoming_edges();
  }
}

void goto_functionst::compute_target_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_target_numbers();
  }
}

void goto_functionst::compute_loop_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_loop_numbers();
  }
}

/// returns a vector of the iterators in alphabetical order
std::vector<goto_functionst::function_mapt::const_iterator>
goto_functionst::sorted() const
{
  std::vector<function_mapt::const_iterator> result;

  result.reserve(function_map.size());

  for(auto it = function_map.begin(); it != function_map.end(); it++)
    result.push_back(it);

  std::sort(
    result.begin(),
    result.end(),
    [](function_mapt::const_iterator a, function_mapt::const_iterator b) {
      return id2string(a->first) < id2string(b->first);
    });

  return result;
}

/// returns a vector of the iterators in alphabetical order
std::vector<goto_functionst::function_mapt::iterator> goto_functionst::sorted()
{
  std::vector<function_mapt::iterator> result;

  result.reserve(function_map.size());

  for(auto it = function_map.begin(); it != function_map.end(); it++)
    result.push_back(it);

  std::sort(
    result.begin(),
    result.end(),
    [](function_mapt::iterator a, function_mapt::iterator b) {
      return id2string(a->first) < id2string(b->first);
    });

  return result;
}
