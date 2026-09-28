extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct traits
{
  template <class U>
  using rebind = U *;
};
template <class A>
struct wrapper
{
  // [temp.names]/3.4: the terminal name of a typename-specifier is in a
  // type-only context ([temp.res.general]/4), so `rebind <' starts a
  // template argument list without the `template' keyword
  typedef typename traits<A>::rebind<int> other;
};
int main()
{
  int x = 3;
  wrapper<char>::other p = &x;
  __CPROVER_assert(*p == 3, "rebound pointer");
  __CPROVER_assert(*p == 4, "WRONG (must FAIL)");
}
