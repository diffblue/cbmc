// N5008 [expr.prim.fold]: a binary right fold.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
int sum(T... t)
{
  return (t + ... + 0);
}
int main()
{
  __CPROVER_assert(sum(1, 2, 3) == 6, "fold expression");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
