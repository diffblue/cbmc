/*******************************************************************\

Module: Prefix Filtering

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Prefix Filtering

#ifndef CPROVER_UTIL_PREFIX_FILTER_H
#define CPROVER_UTIL_PREFIX_FILTER_H

#include <string>
#include <vector>

/// Provides filtering of strings vai inclusion/exclusion lists of prefixes
class prefix_filtert
{
public:
  prefix_filtert(
    std::vector<std::string> included_prefixes,
    std::vector<std::string> excluded_prefixes);

  /// Return true iff \p value matches a prefix in `included_prefixes`,
  /// but doesn't match a prefix in `excluded_prefixes`.
  /// An empty vector of `included_prefixes` is treated as 'match all'.
  /// An empty vector of `excluded_prefixes` is treated as 'match nothing'.
  bool operator()(const std::string &value) const;

protected:
  std::vector<std::string> included_prefixes;
  std::vector<std::string> excluded_prefixes;
};

#endif // CPROVER_UTIL_PREFIX_FILTER_H
