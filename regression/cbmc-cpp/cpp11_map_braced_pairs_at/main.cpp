// C++11 [map.cons]: std::map's initializer_list constructor inserts
// all pairs; [map.access] at() returns a reference to the mapped
// value.  The construction CONVERTS, but verification reports
// "dereference failure: deallocated dynamic object" inside at()'s
// tree walk and the comparator -- the red-black-tree nodes built by
// the initializer_list constructor appear deallocated to the pointer
// checks.  Found while reducing the abstract_environment
// inverse_operations map (this facet reproduces standalone).
// g++/clang++ accept and verify at runtime.
#include <map>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  auto m = std::map<int, int>{{1, 2}, {3, 4}};
  __CPROVER_assert(m.at(1) == 2 && m.at(3) == 4, "map braced pairs");
  return 0;
}
