// std::set reverse iteration relies on std::_Rb_tree_decrement, a libstdc++
// compiled-library helper that CBMC models (cpp_typecheck_stdlib.cpp) as the
// in-order predecessor over the BST, including the header special case
// (decrementing the past-the-end iterator yields the rightmost element).
#include <set>

int main()
{
  std::set<int> s;
  s.insert(42);
  s.insert(17);

  __CPROVER_assert(*s.rbegin() == 42, "rbegin is the largest element");

  int sum = 0;
  unsigned n = 0;
  for(std::set<int>::reverse_iterator it = s.rbegin(); it != s.rend(); ++it)
  {
    sum += *it;
    ++n;
  }
  __CPROVER_assert(n == 2, "reverse iteration visits both elements");
  __CPROVER_assert(sum == 59, "reverse iteration sums the elements");
  return 0;
}
