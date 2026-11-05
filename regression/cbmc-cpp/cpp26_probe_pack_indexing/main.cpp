// N5008 [expr.prim.pack.index]: a pack-index-expression.
extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
int first(T... t)
{
  return t...[0];
}
int main()
{
  __CPROVER_assert(first(4, 5) == 4, "pack indexing");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
