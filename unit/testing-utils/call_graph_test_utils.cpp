/*******************************************************************\

Module: Call graph test utils

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "call_graph_test_utils.h"

#include <util/std_code.h>

symbolt
create_void_function_symbol(const irep_idt &name, const codet &code)
{
  const code_typet void_function_type({}, empty_typet());
  symbolt function;
  function.name = name;
  function.type = void_function_type;
  function.mode = ID_java;
  function.value = code;
  return function;
}

bool multimap_key_matches(
  const std::multimap<irep_idt, irep_idt> &map,
  const irep_idt &key,
  const std::set<irep_idt> &values)
{
  auto matching_values = map.equal_range(key);
  std::set<irep_idt> matching_set;
  for(auto it = matching_values.first; it != matching_values.second; ++it)
    matching_set.insert(it->second);
  return matching_set == values;
}
