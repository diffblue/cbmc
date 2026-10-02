extern "C" void __CPROVER_assert(bool, const char *);
// [dcl.meaning.general]/2.3, [temp.mem.class]/1, [temp.mem.func]/1: the
// member class and the member function of a class template in nested
// namespaces are defined outside the namespaces by qualified names; S<short>
// is instantiated before the member class definition
namespace a
{
namespace b
{
template <class C>
struct S
{
  struct N;
  int f();
};
} // namespace b
} // namespace a
a::b::S<short> early;
template <class C>
struct a::b::S<C>::N
{
  C v = sizeof(C);
};
template <class C>
int a::b::S<C>::f()
{
  N n;
  return n.v;
}
int main()
{
  a::b::S<int> late;
  __CPROVER_assert(early.f() == 2 && late.f() == 4, "nested namespaces");
  __CPROVER_assert(late.f() != 4, "WRONG (must FAIL)");
}
