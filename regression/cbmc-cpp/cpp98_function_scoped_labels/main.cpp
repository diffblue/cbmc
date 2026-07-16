// N5008 [stmt.label]/1: "Labels have their own name space and do not
// interfere with other identifiers. ... A label can be used anywhere in
// the function in which it appears" -- label scope is the FUNCTION, so
// the same label name may be used in different functions.
//
// Regression: the C++ front end accumulated the defined-labels map across
// function bodies, so the second function using a `zero:` label was
// rejected with a spurious "duplicate label" (found by dog-fooding
// CBMC's own big-int/bigint.cc, whose division routines each have a
// `zero:` error path).  g++/clang++ verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

int f(int x)
{
  if(x == 0)
    goto zero;
  return 1;
zero:
  return 0;
}

int g(int x)
{
  if(x == 0)
    goto zero;
  return 3;
zero:
  return 2;
}

int main()
{
  __CPROVER_assert(
    f(0) == 0 && f(1) == 1 && g(0) == 2 && g(1) == 3,
    "function-scoped labels");
  return 0;
}
