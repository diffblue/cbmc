extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct tup;
// N5008 [dcl.spec.auto.general]/13: redeclarations of a function template
// with a placeholder return type use the placeholder; [temp.friend]/1 the
// friend declaration in each tup<...> redeclares the same template
template <int I, class... T>
constexpr auto &&tget(tup<T...> &&t) noexcept;
template <class... T>
struct tup
{
  int v;
  template <int I, class... U>
  friend constexpr auto &&tget(tup<U...> &&t) noexcept;
};
template <int I, class... T>
constexpr auto &&tget(tup<T...> &&t) noexcept
{
  return static_cast<int &&>(t.v);
}
int main()
{
  int a = tget<0>(tup<int>{5});
  tup<long> later{6};
  int b = tget<0>(static_cast<tup<long> &&>(later));
  int c = tget<0>(tup<int>{7});
  __CPROVER_assert(a == 5 && b == 6 && c == 7, "deduced return");
  __CPROVER_assert(a == 0, "WRONG (must FAIL)");
  return 0;
}
