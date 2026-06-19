// [expr.prim.lambda.capture]: a capture-default captures each odr-used entity
// with automatic storage duration -- by copy for `=`, by reference for `&` --
// unless it is explicitly captured otherwise.  A by-copy default capture is a
// snapshot taken at capture time; a by-reference default capture denotes the
// live entity.

int main()
{
  // [=]: used locals captured by copy (snapshot at capture time)
  int a = 3, b = 4;
  auto byval = [=](int x) { return x + a + b; };
  a = 100;
  b = 200; // do not affect the snapshot
  __CPROVER_assert(byval(1) == 8, "[=] snapshots odr-used locals at capture");

  // [&]: used locals captured by reference (live, and modifiable)
  int n = 0;
  auto byref = [&](int x) { n += x; };
  byref(5);
  byref(5);
  __CPROVER_assert(n == 10, "[&] captures odr-used locals by reference");

  // [=, &r]: default copy with an explicit by-reference override
  int c = 1, r = 2;
  auto mixed = [=, &r](int x) { r += x; return c + r; };
  c = 50; // snapshot, unaffected
  int got = mixed(3); // r becomes 2+3=5, returns 1+5 = 6
  __CPROVER_assert(got == 6, "capture-default with explicit override");
  __CPROVER_assert(r == 5, "explicit by-reference override modifies referent");

  return 0;
}
