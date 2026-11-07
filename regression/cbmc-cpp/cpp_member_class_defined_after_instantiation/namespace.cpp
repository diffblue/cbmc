extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
template <class C>
struct S
{
  struct N;
  int f();
};
} // namespace ns
ns::S<char> early;
ns::S<short> early2;
namespace ns
{
template <class C>
struct S<C>::N
{
  C v = sizeof(C);
  explicit operator bool() const
  {
    return v != 0;
  }
};
} // namespace ns
template <class C>
int ns::S<C>::f()
{
  N n;
  if(n)
    return n.v;
  return 0;
}
int main()
{
  ns::S<int> late;
  __CPROVER_assert(early.f() == 1 && early2.f() == 2 && late.f() == 4, "sizes");
  __CPROVER_assert(late.f() != 4, "WRONG (must FAIL)");
}
