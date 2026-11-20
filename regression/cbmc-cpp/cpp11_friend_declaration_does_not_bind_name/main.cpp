extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.meaning.general]/2.1, [basic.lookup.argdep]/4.2: a friend
// declaration does not bind a name, so the friend h(int) of A is found only
// by argument-dependent lookup with A an associated class; h(0) calls
// ::h(long).  A later namespace-scope declaration binds the name of k.
struct A
{
  friend int h(int)
  {
    return 1;
  }
  friend int h(const A &)
  {
    return 3;
  }
  friend int k(int)
  {
    return 4;
  }
};
int h(long)
{
  return 2;
}
int k(int);
int main()
{
  __CPROVER_assert(h(0) == 2, "hidden friend not found by ordinary lookup");
  __CPROVER_assert(h(A{}) == 3, "found by argument-dependent lookup");
  __CPROVER_assert(k(0) == 4, "declared at namespace scope");
  __CPROVER_assert(h(0) == 1, "WRONG (must FAIL)");
  return 0;
}
