// C++11 [map.cons]: std::map's initializer_list constructor inserts
// all pairs; [map.access] at() returns a reference to the mapped
// value.  Verification used to report "deallocated dynamic object"
// inside at()'s tree walk: `auto m = ...` bitwise-copied the
// materialized temporary and then ran ITS destructor, freeing the
// tree nodes m still referenced -- fixed 2026-07-21 (route through
// the move constructor, [dcl.init]/16.6.2).  Found while reducing the abstract_environment
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
