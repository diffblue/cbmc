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

void goto_functionst::validate(const namespacet &ns, const validation_modet vm)
  const
{
  for(const auto &entry : function_map)
  {
    const goto_functiont &goto_function = entry.second;
    const auto &function_name = entry.first;
    const symbolt &function_symbol = ns.lookup(function_name);
    const code_typet::parameterst &parameters =
      to_code_type(function_symbol.type).parameters();

    DATA_CHECK(
      vm,
      goto_function.type == ns.lookup(function_name).type,
      id2string(function_name) + " type inconsistency\ngoto program type: " +
        goto_function.type.id_string() +
        "\nsymbol table type: " + ns.lookup(function_name).type.id_string());

    DATA_CHECK(
      vm,
      goto_function.parameter_identifiers.size() == parameters.size(),
      id2string(function_name) + " parameter count inconsistency\n" +
        "goto program: " +
        std::to_string(goto_function.parameter_identifiers.size()) +
        "\nsymbol table: " + std::to_string(parameters.size()));

    auto it = goto_function.parameter_identifiers.begin();
    for(const auto &parameter : parameters)
    {
      DATA_CHECK(
        vm,
        it->empty() || ns.lookup(*it).type == parameter.type(),
        id2string(function_name) + " parameter type inconsistency\n" +
          "goto program: " + ns.lookup(*it).type.id_string() +
          "\nsymbol table: " + parameter.type().id_string());
      ++it;
    }

    goto_function.validate(ns, vm);
  }
}
