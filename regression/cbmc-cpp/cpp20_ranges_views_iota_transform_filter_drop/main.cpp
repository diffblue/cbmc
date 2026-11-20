// Regression guard: N5008 [range.iota], [range.transform], [range.filter],
// [range.drop] -- the views compose with a range-based for loop.  These were
// open in round 176 (the __tuple_impl layer) and work now with libstdc++ and
// libc++; no test covered them.
extern "C" void __CPROVER_assert(bool, const char *);
#include <ranges>
int main()
{
  int s = 0;
  for(int x : std::views::iota(1, 4))
    s += x;
  __CPROVER_assert(s == 6, "iota");
  int a[4] = {1, 2, 3, 4};
  s = 0;
  for(int x : a | std::views::transform([](int v) { return 2 * v; }))
    s += x;
  __CPROVER_assert(s == 20, "transform");
  s = 0;
  for(int x : a | std::views::filter([](int v) { return v % 2 == 0; }))
    s += x;
  __CPROVER_assert(s == 6, "filter");
  s = 0;
  for(int x : a | std::views::drop(1))
    s += x;
  __CPROVER_assert(s == 9, "drop");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
