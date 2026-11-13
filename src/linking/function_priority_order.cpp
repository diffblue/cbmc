/*******************************************************************\

Module: Ordering of constructor/destructor functions by GCC priority

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Ordering of constructor/destructor functions by their GCC priority
/// attribute

#include "function_priority_order.h"

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <algorithm>

mp_integer function_priority(const symbolt &symbol)
{
  const exprt &priority = static_cast<const exprt &>(
    to_code_type(symbol.type).return_type().find(ID_priority));
  if(priority.is_nil())
    return DEFAULT_FUNCTION_PRIORITY;

  const auto value = numeric_cast<mp_integer>(priority);
  DATA_INVARIANT(
    value.has_value(), "type checking makes the priority a constant");
  return *value;
}

std::vector<std::reference_wrapper<const symbolt>> order_functions_by_priority(
  const std::vector<std::reference_wrapper<const symbolt>> &functions,
  function_priority_ordert order)
{
  std::vector<std::pair<mp_integer, std::reference_wrapper<const symbolt>>>
    prioritised;
  prioritised.reserve(functions.size());
  for(const auto &function : functions)
    prioritised.emplace_back(function_priority(function.get()), function);

  // ascending priority, keeping the given order for equal priorities
  std::stable_sort(
    prioritised.begin(),
    prioritised.end(),
    [](const auto &a, const auto &b) { return a.first < b.first; });

  std::vector<std::reference_wrapper<const symbolt>> result;
  result.reserve(prioritised.size());
  for(const auto &entry : prioritised)
    result.push_back(entry.second);

  if(order == function_priority_ordert::DESCENDING)
    std::reverse(result.begin(), result.end());

  return result;
}
