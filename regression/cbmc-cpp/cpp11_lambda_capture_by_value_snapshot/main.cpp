// [expr.prim.lambda.capture]: "For each entity captured by copy, an unnamed
// non-static data member is declared in the closure type", direct-initialised
// from the entity at the point the closure object is created.  A by-copy
// capture is therefore a *snapshot* taken at capture time; later modifications
// to the original variable are not observed by the closure.
//
// KNOWNBUG (unsound): CBMC stores a capture as a shared file-local symbol that
// is read at *call* time, so a by-copy capture behaves like a by-reference
// capture and observes the post-capture value.  Here `f` captures a==10 by
// copy; after `a` is changed to 20, `f(5)` must still compute 5+10==15.
// Reclassify CORE once by-copy captures snapshot at capture time.
int main()
{
  int a = 10;
  auto f = [a](int x) { return x + a; };
  a = 20;
  __CPROVER_assert(f(5) == 15, "by-copy capture snapshots the value at capture time");
  return 0;
}
