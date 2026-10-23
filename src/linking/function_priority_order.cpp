/*******************************************************************\

Module: Ordering of constructor/destructor functions by GCC priority

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Ordering of constructor/destructor functions by their GCC priority
/// attribute

#include "function_priority_order.h"

#include <map>

std::list<std::reference_wrapper<const symbolt>> order_functions_by_priority(
  const std::list<
    std::pair<std::reference_wrapper<const symbolt>, std::optional<mp_integer>>>
    &functions,
  function_priority_ordert order)
{
  // Bucket the prioritised functions by their (actual, non-negated) priority,
  // keeping the unprioritised ones separate. Within a bucket the source order
  // is preserved as functions are appended.
  std::map<mp_integer, std::list<std::reference_wrapper<const symbolt>>>
    by_priority;
  std::list<std::reference_wrapper<const symbolt>> without_priority;

  for(const auto &function : functions)
  {
    if(function.second.has_value())
      by_priority[*function.second].push_back(function.first);
    else
      without_priority.push_back(function.first);
  }

  std::list<std::reference_wrapper<const symbolt>> result;

  if(order == function_priority_ordert::ASCENDING)
  {
    // ascending priority, unprioritised functions last
    for(auto &priority_pair : by_priority)
      result.splice(result.end(), priority_pair.second);
    result.splice(result.end(), without_priority);
  }
  else
  {
    // unprioritised functions first, then descending priority
    result.splice(result.end(), without_priority);
    for(auto it = by_priority.rbegin(); it != by_priority.rend(); ++it)
      result.splice(result.end(), it->second);
  }

  return result;
}
