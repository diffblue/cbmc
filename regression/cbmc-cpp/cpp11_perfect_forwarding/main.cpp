// C++11 perfect forwarding
template <typename T>
T &&forward(T &t)
{
  return static_cast<T &&>(t);
}
struct S
{
  int x;
  S(int v) : x(v)
  {
  }
};
template <typename T, typename Arg>
T create(Arg &&arg)
{
  return T(forward<Arg>(arg));
}
int main()
{
  S s = create<S>(42);
  __CPROVER_assert(s.x == 42, "perfect forwarding");
  return 0;
}
