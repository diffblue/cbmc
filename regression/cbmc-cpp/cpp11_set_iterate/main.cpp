// std::set forward iteration relies on std::_Rb_tree_increment, a
// libstdc++ compiled-library helper that CBMC models (cpp_typecheck_stdlib.cpp)
// as the in-order successor over the binary-search-tree structure.
#include <set>

int main()
{
  std::set<int> s;
  s.insert(42);
  s.insert(17);

  int sum = 0;
  unsigned n = 0;
  for(std::set<int>::iterator it = s.begin(); it != s.end(); ++it)
  {
    sum += *it;
    ++n;
  }
  __CPROVER_assert(n == 2, "forward iteration visits both elements");
  __CPROVER_assert(sum == 59, "forward iteration sums the elements");
  return 0;
}
