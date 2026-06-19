// [expr.prim.lambda.closure]: the closure type's function call operator is
// const-qualified unless the lambda is declared mutable.  A mutable lambda's
// by-copy captures are mutable non-static data members of the closure object,
// so modifications persist in that object across calls.
//
// KNOWNBUG (unsound): CBMC has no per-object closure state, so a mutable
// lambda's captured counter does not persist across calls.  Here the captured
// `a` starts at 10; the first call returns 11 and the second 12.
// Reclassify CORE once mutable lambdas have persistent per-object capture state.
int main()
{
  int a = 10;
  auto f = [a]() mutable { a += 1; return a; };
  int r1 = f();
  int r2 = f();
  __CPROVER_assert(
    r1 == 11 && r2 == 12, "mutable lambda keeps per-object capture state");
  return 0;
}
