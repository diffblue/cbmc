// N5008 [dcl.attr.nouniqueaddr]/1: an empty [[no_unique_address]] member is
// an object of its class: it is initialized by its constructors
// ([class.base.init]/7), aggregate-initialized, accessed, and named by
// decltype ([dcl.type.decltype]/1.3) as any other member.
#include <cstddef>
#include <type_traits>
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);
int constructed = 0;
int destroyed = 0;
struct D
{
  ~D()
  {
    ++destroyed;
  }
};
struct WithD
{
  [[no_unique_address]] D d;
  int i;
};
struct E
{
  constexpr int get() const
  {
    return 7;
  }
  const E *self() const
  {
    return this;
  }
};
struct C
{
  C()
  {
    ++constructed;
  }
  C(const C &)
  {
    ++constructed;
  }
};
struct S
{
  char d[3];
  [[no_unique_address]] E e;
  char c;
};
struct T
{
  [[no_unique_address]] C counted;
  [[no_unique_address]] E e;
  int i;
  T() : i(5)
  {
  }
  explicit T(int v) : counted(), e(E{}), i(v)
  {
  }
};
template <class A>
struct Holder
{
  [[no_unique_address]] A alloc;
  int *p;
  Holder(A a, int *q) : alloc(std::move(a)), p(q)
  {
  }
};
int main()
{
  S s{{'a', 'b', 'c'}, {}, 'd'};
  __CPROVER_assert(sizeof(S) == 4 && s.d[0] == 'a' && s.c == 'd', "aggregate");
  __CPROVER_assert(s.e.get() == 7 && s.e.self() == &s.e, "member call");
  __CPROVER_assert((char *)&s.e == (char *)&s, "at offset 0");
  static_assert(std::is_same<decltype(s.e), E>::value, "decltype(s.e)");
  static_assert(std::is_same<decltype((s.e)), E &>::value, "decltype((s.e))");
  T t;
  T u(9);
  T w = u;
  __CPROVER_assert(sizeof(T) == 4 && t.i == 5 && u.i == 9 && w.i == 9, "T");
  __CPROVER_assert(constructed == 3, "constructors of an empty member run");
  int x = 1;
  Holder<E> h(E{}, &x);
  __CPROVER_assert(sizeof(h) == sizeof(int *) && *h.p == 1, "Holder");
  __CPROVER_assert(offsetof(S, e) == 0, "offsetof");
  E S::*pm = &S::e;
  __CPROVER_assert(&(s.*pm) == &s.e, "pointer to member");
  constexpr S cs{};
  static_assert(cs.e.get() == 7, "constant evaluation");
  {
    WithD wd;
    wd.i = 1;
  }
  __CPROVER_assert(destroyed == 1, "destructor of an empty member runs");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
