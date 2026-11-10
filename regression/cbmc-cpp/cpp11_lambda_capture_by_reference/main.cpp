// [expr.prim.lambda.capture]: an entity captured by reference is captured as a
// reference -- a reference member of the closure that denotes the entity.  A
// by-reference capture therefore observes the live entity (including later
// modifications) and, through the reference, can modify it; a const (non-
// mutable) lambda may still modify the referenced entity through the reference.

int main()
{
  // by-reference capture observes later modifications of the entity
  int a = 10;
  auto f = [&a](int x) { return x + a; };
  a = 20;
  __CPROVER_assert(f(5) == 25, "by-ref capture observes the live entity");

  // through the reference, the lambda modifies the referenced entity
  int n = 0;
  auto inc = [&n]() { n += 1; };
  inc();
  inc();
  __CPROVER_assert(n == 2, "by-ref capture modifies the referenced entity");

  // mixed: by-copy c (snapshot) and by-reference r
  int c = 3, r = 4;
  auto g = [c, &r](int x) { return x + c + r; };
  c = 100; // does not affect the snapshot
  r = 5;   // does affect the reference
  __CPROVER_assert(g(1) == 9, "mixed by-copy snapshot and by-reference live");

  return 0;
}
