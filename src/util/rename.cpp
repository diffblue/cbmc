/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename.h"

#include "namespace.h"

#include <string>
#include <unordered_map>

/// Produce a fresh name by appending delimiter + number to \p name.
/// Uses a per-prefix counter to avoid O(n) probing of the symbol table
/// on each call. Falls back to symbol table probing only on the first
/// call for each prefix.
irep_idt
get_new_name(const irep_idt &name, const namespacet &ns, char delimiter)
{
  const symbolt *symbol;
  if(ns.lookup(name, symbol))
    return name;

  std::string prefix = id2string(name) + delimiter;

  // Cache the next suffix to try for each prefix. This turns the O(n)
  // linear probe in smallest_unused_suffix into amortized O(1).
  // thread_local for safety in case of future multi-threading.
  static thread_local std::unordered_map<std::string, std::size_t> suffix_cache;
  auto it = suffix_cache.find(prefix);
  std::size_t suffix;
  if(it != suffix_cache.end())
    suffix = it->second;
  else
    suffix = ns.smallest_unused_suffix(prefix);

  // Verify the suffix is actually unused
  while(!ns.lookup(prefix + std::to_string(suffix), symbol))
    ++suffix;

  suffix_cache[prefix] = suffix + 1;
  return prefix + std::to_string(suffix);
}
