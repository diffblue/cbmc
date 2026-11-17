extern "C" void __CPROVER_assert(bool, const char *);
template <typename T>
int size_of(T)
{
  return sizeof(T);
}
template <typename>
void size_of();
struct result
{
  int sum;
};
int add_all(int a, int b, int c)
{
  return a + b + c;
}
struct box
{
  int total = 0;
  template <typename... A>
  constexpr result add(A... a)
  {
    ((total += size_of<A>(a)), ...);
    return result{total};
  }
  template <typename... A>
  void add_all(A... a)
  {
    ((total += size_of<A>(a)), ...);
  }
  template <typename... A>
  constexpr result call(A... a)
  {
    return result{::add_all(size_of<A>(a)...)};
  }
};
int main()
{
  box b;
  result r = b.add(1, 'c', 2.0);
  __CPROVER_assert(r.sum == 4 + 1 + 8, "constexpr member template");
  box c;
  c.add_all('c', 1, 2.0);
  __CPROVER_assert(c.total == 1 + 4 + 8, "member template");
  result s = c.call(2.0, 'c', 1);
  __CPROVER_assert(s.sum == 8 + 1 + 4, "call argument expansion");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
