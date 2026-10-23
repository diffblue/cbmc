extern "C" void __CPROVER_assert(bool, const char *);
// [dcl.typedef]/2, [temp.variadic]/5: member alias-declarations of function
// type whose parameter list is a pack expansion, for empty, three-element
// and reference packs, and patterns `T &...' and `T &&...'
int hit;
void c0()
{
  hit = 9;
}
void c3(int a, char, long)
{
  hit = a;
}
void cr(int &r, const char *)
{
  r = 5;
}
template <class... T>
struct X
{
  using F = void(T...);
  F *p;
  using G = int(T &...);
};
template <class R, class... T>
struct Y
{
  using F = R(T &&...) noexcept;
};
template <class A, class B>
struct same
{
  static const bool value = false;
};
template <class A>
struct same<A, A>
{
  static const bool value = true;
};
int main()
{
  X<> e;
  e.p = c0;
  e.p();
  __CPROVER_assert(hit == 9, "empty pack");
  X<int, char, long> x;
  x.p = c3;
  x.p(4, 'c', 1L);
  __CPROVER_assert(hit == 4, "three elements");
  X<int &, const char *> y;
  y.p = cr;
  int k = 0;
  y.p(k, "s");
  __CPROVER_assert(k == 5, "reference element");
  __CPROVER_assert(
    same<X<int, char>::G, int(int &, char &)>::value, "pattern T &...");
  __CPROVER_assert(
    same<Y<int, long>::F, int(long &&) noexcept>::value,
    "pattern T &&... noexcept");
  __CPROVER_assert(hit != 4, "WRONG (must FAIL)");
}
