/*******************************************************************\

 Module: functions that are useful with optionalt

 Author: Diffblue Ltd.

\*******************************************************************/

#include "optional.h"

#include <iterator>
#include <map>

/// Lookup a key in a map, if found return the associated value, nullopt otherwise
template <typename map_like_collectiont, typename keyt>
auto optional_lookup(const map_like_collectiont &map, const keyt &key)
  -> optionalt<decltype(map.find(key)->second)>
{
  auto const it = map.find(key);
  if(it != map.end())
  {
    return it->second;
  }
  return nullopt;
}
