/*******************************************************************\

Module: functions that are useful with std::optional

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_OPTIONAL_UTILS_H
#define CPROVER_UTIL_OPTIONAL_UTILS_H

#include <optional>

/// Lookup a key in a map, if found return the associated value,
/// nullopt otherwise
template <typename map_like_collectiont, typename keyt>
auto optional_lookup(const map_like_collectiont &map, const keyt &key)
  -> std::optional<decltype(map.find(key)->second)>
{
  auto const it = map.find(key);
  if(it != map.end())
  {
    return it->second;
  }
  return {};
}

#endif // CPROVER_UTIL_OPTIONAL_UTILS_H
