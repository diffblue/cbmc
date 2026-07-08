// N5008 [dcl.array]/1 and [dcl.init.aggr]/5: an array of unknown bound whose
// declaration has a brace-enclosed initializer list has its bound deduced from
// the number of initializer-clauses.  This holds whether or not the element
// type has a user-provided constructor.
//
// Regression test for bound deduction of `T a[]{...}` where T has a
// user-provided constructor.  Previously the front-end deduced the bound only
// for scalar/trivial element types; for a constructible element type it went
// through per-element construction with a nil (undeduced) array size and failed
// with "expected constant expression" (and left the array type incomplete, so
// sizeof failed).  This is what made src/util/simplify_utils.cpp -- which
// instantiates std::optional<std::pair<...>> over non-trivial CBMC types --
// fail to compile with goto-cc.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct S
{
  int v;
  S(int x) : v(x)
  {
  }
};

int main()
{
  S a[]{S(10), S(20), S(30)}; // unknown bound: deduced to 3

  __CPROVER_assert(
    sizeof(a) / sizeof(a[0]) == 3,
    "array bound deduced from initializer count");
  __CPROVER_assert(
    a[0].v == 10 && a[1].v == 20 && a[2].v == 30, "each element initialized");
  __CPROVER_assert(a[1].v != 20, "WRONG must FAIL");
  return 0;
}
