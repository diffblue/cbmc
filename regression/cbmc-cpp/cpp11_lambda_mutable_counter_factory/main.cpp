// [expr.prim.lambda.closure]/1 + [expr.prim.lambda.closure]: each closure is a
// distinct object; a mutable lambda's by-copy captures are mutable members, so
// counters created by a factory have independent, persistent state.
#include <functional>

auto make_counter(int start)
{
  return [start]() mutable { return start++; };
}

int main()
{
  auto c1 = make_counter(100);
  auto c2 = make_counter(200);

  int a = c1(); // 100
  int b = c1(); // 101
  int d = c2(); // 200 -- independent of c1
  int e = c1(); // 102

  __CPROVER_assert(a == 100, "first counter starts at 100");
  __CPROVER_assert(b == 101, "first counter increments");
  __CPROVER_assert(d == 200, "second counter is independent");
  __CPROVER_assert(e == 102, "first counter continues after second is used");
  return 0;
}
