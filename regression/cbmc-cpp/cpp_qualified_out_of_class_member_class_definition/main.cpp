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
// [temp.mem.class]/1, [class.nest]/3: the member class is defined outside
// its namespace by a qualified name
template <class C>
struct ns::S<C>::N
{
  int v = 7;
};
template <class C>
int ns::S<C>::f()
{
  N n;
  return n.v;
}
int main()
{
  ns::S<char> s;
  __CPROVER_assert(s.f() == 7, "qualified member class definition");
  __CPROVER_assert(s.f() != 7, "WRONG (must FAIL)");
}
