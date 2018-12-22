/*******************************************************************\

Module: Container utilities

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_CONTAINER_UTILS_H
#define CPROVER_UTIL_CONTAINER_UTILS_H

#include <set>

/// Compute union of two sets
///
/// This function has complexity O(max(n1, n2)), with n1, n2 being the sizes of
/// the sets of which the union is formed. This is in contrast to
/// `target.insert(source.begin(), source.end())` which has complexity
/// O(n2 * log(n1 + n2)).
///
/// \tparam T: value type of the sets
/// \tparam Compare: comparison predicate of the sets
/// \tparam Alloc: allocator of the sets
/// \param target: first input set, will contain the result of the union
/// \param source: second input set
/// \return true iff `target` was changed
template <class T, class Compare, class Alloc>
bool util_inplace_set_union(
  std::set<T, Compare, Alloc> &target,
  const std::set<T, Compare, Alloc> &source)
{
  bool changed = false;
  typename std::set<T, Compare, Alloc>::iterator it = target.begin();

  for(const auto &s : source)
  {
    while(it != target.end() && *it < s)
    {
      ++it;
    }

    if(it == target.end() || s < *it)
    {
      // Insertion hint should point at element that will follow the new element
      target.insert(it, s);
      changed = true;
    }
    else if(it != target.end())
    {
      ++it;
    }
  }

  return changed;
}

#endif // CPROVER_UTIL_CONTAINER_UTILS_H
