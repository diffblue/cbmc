// std::set erase relies on std::_Rb_tree_rebalance_for_erase, a libstdc++
// compiled-library helper that CBMC models (cpp_typecheck_stdlib.cpp) as the
// binary-search-tree erase (the three structural cases, including splicing in
// the in-order successor for a two-child node) plus header (root / leftmost /
// rightmost) maintenance.  The red-black rebalancing is omitted as it does not
// affect ordered-container semantics.
//
// Both the iterator overload erase(iterator) and the key overload erase(key)
// are exercised; erase(key) additionally goes through equal_range, which
// returns a std::pair<iterator, iterator> by value.
#include <set>

int main()
{
  std::set<int> s;
  s.insert(50);
  s.insert(30);
  s.insert(70);

  // Erase the root, a node with two children: the in-order successor (70) is
  // spliced into its place.
  s.erase(s.find(50));
  __CPROVER_assert(s.size() == 2, "size after two-child erase");
  __CPROVER_assert(s.count(50) == 0, "erased element absent");
  __CPROVER_assert(s.count(30) == 1, "left child still present");
  __CPROVER_assert(s.count(70) == 1, "right child still present");

  // The tree is still a valid ordered container after erase.
  int prev = -1;
  bool sorted = true;
  for(std::set<int>::iterator it = s.begin(); it != s.end(); ++it)
  {
    if(*it <= prev)
      sorted = false;
    prev = *it;
  }
  __CPROVER_assert(sorted, "still sorted after erase");
  __CPROVER_assert(
    *s.begin() == 30 && *s.rbegin() == 70, "min and max correct after erase");

  // Erase by key: goes through equal_range (which returns a pair by value).
  std::set<int>::size_type n = s.erase(30);
  __CPROVER_assert(n == 1, "erase(key) reports one element removed");
  __CPROVER_assert(s.size() == 1, "size after erase(key)");
  __CPROVER_assert(s.count(30) == 0, "erased key absent");
  __CPROVER_assert(*s.begin() == 70, "remaining element is 70");

  // Erasing an absent key removes nothing.
  __CPROVER_assert(s.erase(12345) == 0, "erase of absent key removes nothing");
  return 0;
}
