extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct S
{
  struct N;
  int f();
};
// S<char> is implicitly instantiated here, while S<C>::N is still only
// declared
S<char> early;
// [temp.mem.class]/1: the member class is defined outside the class template
template <class C>
struct S<C>::N
{
  int v = 7;
};
// [temp.inst]/3: S<char>::N is implicitly instantiated where its
// completeness is required -- in the instantiated f, after its definition
// (libstdc++: `template basic_istream<char> &basic_istream<char>::
// ignore(streamsize);' in <istream> before istream.tcc defines
// basic_istream<_CharT, _Traits>::sentry)
template <class C>
int S<C>::f()
{
  N n;
  return n.v;
}
int main()
{
  __CPROVER_assert(early.f() == 7, "member class defined after");
  __CPROVER_assert(early.f() != 7, "WRONG (must FAIL)");
}
