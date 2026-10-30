extern "C" void __CPROVER_assert(bool, const char *);
template <class... Ts>
int bytes(Ts...)
{
  // [expr.prim.fold]/2: the pattern names the TYPE pack
  return (0 + ... + static_cast<int>(sizeof(Ts)));
}
int main()
{
  __CPROVER_assert(bytes('a', 1, 2.0) == 1 + 4 + 8, "sizeof of each type");
  __CPROVER_assert(bytes('a', 1, 2.0) == 3, "WRONG (must FAIL)");
}
