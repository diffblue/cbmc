extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
constexpr int f()
{
  return 5;
}
template <class... Ts>
int count()
{
  int a[] = {1, f<Ts>()...};
  return sizeof(a) / sizeof(a[0]);
}
template <class... Ts>
int count_sizeof()
{
  unsigned long a[] = {1, sizeof(Ts)...};
  return sizeof(a) / sizeof(a[0]);
}
template <class... Ts>
constexpr int last()
{
  // constant-evaluated: the pack expansion must be empty for Ts = {}
  constexpr int a[] = {7, f<Ts>()...};
  return a[sizeof...(Ts)];
}
static_assert(last<>() == 7, "empty pack: only the first element");
static_assert(last<int>() == 5, "one element");
int main()
{
  __CPROVER_assert(count<>() == 1, "empty pack: one element");
  __CPROVER_assert(count<int, char>() == 3, "two: three elements");
  __CPROVER_assert(count_sizeof<>() == 1, "sizeof pattern, empty pack");
  __CPROVER_assert(count<>() == 2, "WRONG (must FAIL)");
}
