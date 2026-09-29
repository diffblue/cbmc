extern "C" void __CPROVER_assert(bool, const char *);
template <class... Ts>
int bytes(Ts... xs)
{
  // [expr.prim.fold]/2 + [expr.sizeof]/1: each element of the expansion is
  // sizeof applied to one pack element
  return (0 + ... + static_cast<int>(sizeof(xs)));
}
int main()
{
  __CPROVER_assert(bytes('a', 1, 2.0) == 1 + 4 + 8, "sizeof of each element");
  __CPROVER_assert(bytes('a', 1, 2.0) == 3, "WRONG (must FAIL)");
}
