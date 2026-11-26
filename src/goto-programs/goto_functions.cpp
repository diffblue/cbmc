/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#include "goto_functions.h"

#include <util/exception_utils.h>
#include <util/namespace.h>
#include <util/symbol.h>

#include <algorithm>

void goto_functionst::compute_location_numbers()
{
  unused_location_number = 0;
  auto sorted_funcs = sorted();
  for(auto &it : sorted_funcs)
  {
    // Side-effect: bumps unused_location_number.
    it->second.body.compute_location_numbers(unused_location_number);
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

    // Check that a void function does not contain any RETURN instructions
    if(to_code_type(function_symbol.type).return_type().id() == ID_empty)
    {
      for(const auto &instruction : goto_function.body.instructions)
      {
        DATA_CHECK(
          vm,
          !instruction.is_set_return_value(),
          "void function should not return a value");
      }
    }
  }
}

void goto_functionst::validate_numbering(const validation_modet vm) const
{
  struct location_number_ranget
  {
    unsigned first;
    unsigned last;
    irep_idt function_id;
  };

  std::vector<location_number_ranget> ranges;

  for(const auto &entry : function_map)
  {
    const auto &function_id = entry.first;
    const goto_functiont &goto_function = entry.second;
    if(!goto_function.body_available())
      continue;

    const goto_programt &body = goto_function.body;
    try
    {
      body.validate_numbering(validation_modet::EXCEPTION);
    }
    catch(const incorrect_goto_program_exceptiont &exception)
    {
      // Report in the requested mode, with the name of the function
      DATA_CHECK_WITH_DIAGNOSTICS(
        vm,
        false,
        "the instruction numbers of a function body are not valid",
        "function " + id2string(function_id),
        exception.what());
    }

    // The location numbers of a body increase, so the last one is the largest
    const unsigned last = body.instructions.back().location_number;
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      last < unused_location_number,
      "location numbers must be below the unused location number",
      "function " + id2string(function_id) + " has location number " +
        std::to_string(last) + ", the unused location number is " +
        std::to_string(unused_location_number));

    ranges.push_back(
      {body.instructions.front().location_number, last, function_id});
  }

  std::sort(
    ranges.begin(),
    ranges.end(),
    [](const location_number_ranget &a, const location_number_ranget &b)
    {
      return a.first != b.first
               ? a.first < b.first
               : id2string(a.function_id) < id2string(b.function_id);
    });

  for(std::size_t i = 1; i < ranges.size(); ++i)
  {
    const location_number_ranget &previous = ranges[i - 1];
    const location_number_ranget &next = ranges[i];
    DATA_CHECK_WITH_DIAGNOSTICS(
      vm,
      previous.last < next.first,
      "the location numbers of functions " + id2string(previous.function_id) +
        " and " + id2string(next.function_id) + " overlap",
      "function " + id2string(previous.function_id) + " has location numbers " +
        std::to_string(previous.first) + " to " + std::to_string(previous.last),
      "function " + id2string(next.function_id) + " has location numbers " +
        std::to_string(next.first) + " to " + std::to_string(next.last));
  }
}
