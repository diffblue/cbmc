// [expr.prim.lambda.closure]/1: each lambda-expression has a unique closure
// *object*; captures are non-static data members of that object.  Distinct
// closure objects therefore have independent capture storage, so a "factory"
// that returns a fresh capturing lambda per call yields independent closures.
//
// KNOWNBUG (unsound): CBMC stores a lambda's capture in a single shared
// file-local symbol, so two closures of the same lambda type share capture
// storage -- the second construction overwrites the first.  Here make_adder(3)
// and make_adder(10) must be independent (a3(1)==4 and a10(1)==11).
// Reclassify CORE once captures are per-object closure members.
auto make_adder(int n)
{
  return [n](int x) { return x + n; };
}

int main()
{
  auto a3 = make_adder(3);
  auto a10 = make_adder(10);
  __CPROVER_assert(a3(1) == 4, "first closure keeps its own capture");
  __CPROVER_assert(a10(1) == 11, "second closure keeps its own capture");
  return 0;
}
