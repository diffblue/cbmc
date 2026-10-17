extern "C" void __CPROVER_assert(bool, const char *);
template <class... T>
struct list
{
  static constexpr int size = sizeof...(T);
};
template <class L1, class L2>
int sizes(L1, L2, int)
{
  return 10 * L1::size + L2::size;
}
// N5008 [temp.variadic]/7: an expansion of an empty pack nested in an
// argument, in a template argument list, yields an empty list there; the
// argument itself remains
struct member
{
  int v;
  template <class... T1, class... T2>
  member(list<T1...>, list<T2...>) : v(sizes(list<T1...>{}, list<T2...>{}, 0))
  {
  }
};
struct delegating
{
  int a, b;
  template <class... T1, class... T2>
  delegating(int, list<T1...>, list<T2...>)
    : delegating(list<T1...>{}, list<T2...>{}, 0)
  {
  }

private:
  template <class L1, class L2>
  delegating(L1, L2, int) : a(L1::size), b(L2::size)
  {
  }
};
int main()
{
  member m(list<int, char>{}, list<>{});
  delegating d(0, list<int, char>{}, list<>{});
  __CPROVER_assert(m.v == 20, "member initializer");
  __CPROVER_assert(d.a == 2 && d.b == 0, "delegating constructor");
  __CPROVER_assert(d.b == 1, "WRONG (must FAIL)");
  return 0;
}
