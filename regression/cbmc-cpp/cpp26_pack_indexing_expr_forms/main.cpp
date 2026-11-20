// N5008 [expr.prim.pack.index]: pack-index-expressions.
extern "C" void __CPROVER_assert(bool, const char *);
template <typename... Ts>
auto first(Ts... ts)
{
  return ts...[0];
}
template <typename... Ts>
auto last(Ts... ts)
{
  return ts...[sizeof...(ts) - 1];
}
template <typename... Ts>
auto second_plus_first(Ts... ts)
{
  return ts...[1] + ts...[0];
}
template <typename... Ts>
constexpr auto cfirst(Ts... ts)
{
  return ts...[0];
}
int main()
{
  __CPROVER_assert(first(42, 2, 3) == 42, "first of three");
  __CPROVER_assert(first(7) == 7, "first of one");
  __CPROVER_assert(
    last(1, 2, 3.5) == 3.5, "last, index is a constant expression");
  __CPROVER_assert(second_plus_first(10, 5) == 15, "two indexings");
  static_assert(cfirst(9, 8) == 9, "constexpr");
  __CPROVER_assert(first(1, 2) == 2, "WRONG (must FAIL)");
  return 0;
}
