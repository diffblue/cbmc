// N5008 [expr.prim.this]/4, [expr.prim.id.general]/2: in a member
// function's trailing-return-type, a non-static data member's name stands
// for (*this).m, an lvalue ([expr.prim.id.unqual]/3, [expr.ref]/6.2), so it
// binds to the `int &' parameter of hr.  It was treated as a prvalue and
// the declaration failed ("found no match for symbol 'hr'").
extern "C" void __CPROVER_assert(bool, const char *);

int hr(int &)
{
  return 1;
}

template <int I, class... T>
struct tup
{
};

template <int I, class T>
constexpr int get(tup<I, T> &)
{
  return I;
}

struct plain
{
  int n;
  tup<4, int> bound;
  auto g() -> decltype(hr(n))
  {
    return 10;
  }
  template <class A>
  auto f(A) -> decltype(hr(n))
  {
    return 20;
  }
  template <class... A>
  auto h(A...) -> decltype(get<4>(bound))
  {
    return get<4>(bound);
  }
};

int main()
{
  plain p;
  __CPROVER_assert(p.g() == 10 && p.f(0) == 20, "member as lvalue");
  __CPROVER_assert(p.h() == 4, "member template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
