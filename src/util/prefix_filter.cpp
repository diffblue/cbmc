/*******************************************************************\

Module: Prefix Filtering

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Prefix Filtering

#include "prefix_filter.h"

#include <algorithm>

#include "prefix.h"

prefix_filtert::prefix_filtert(
  std::vector<std::string> included_prefixes,
  std::vector<std::string> excluded_prefixes)
  : included_prefixes(std::move(included_prefixes)),
    excluded_prefixes(std::move(excluded_prefixes))
{
}

bool prefix_filtert::operator()(const std::string &value) const
{
  if(!included_prefixes.empty())
  {
    // We don't include everything, so let's check whether value is included.
    const bool matches_included = std::any_of(
      included_prefixes.begin(),
      included_prefixes.end(),
      [value](const std::string &prefix) { return has_prefix(value, prefix); });
    if(!matches_included)
      return false;
  }

  // We know it's included so let's check whether it's excluded.
  const bool matches_excluded = std::any_of(
    excluded_prefixes.begin(),
    excluded_prefixes.end(),
    [value](const std::string &prefix) { return has_prefix(value, prefix); });
  return !matches_excluded;
}
