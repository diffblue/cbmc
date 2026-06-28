// N5008 [temp.variadic]/5 (member-initializer pack expansion): a constructor
// whose member/base initializer contains a pack expansion `t...` over a
// parameter pack of length N forwards the N corresponding constructor
// arguments to that initializer.  Here a class template partial specialization
// `D<H, T...>` (the shape of libstdc++'s _Tuple_impl recursion step) forwards a
// two-element trailing pack to a fixed-arity base initializer
// `Triple(h, t...)`.
//
// Header-free and non-vacuous: assertion 3 is a deliberately wrong claim that
// must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

struct Triple
{
  int x, y, z;
  Triple(int a, int b, int c) : x(a), y(b), z(c) {}
};

template <class...>
struct D
{
  int tag;
  D() : tag(0) {}
};

template <class H, class... T>
struct D<H, T...> : Triple
{
  D(const H &h, const T &... t) : Triple(h, t...) {}
};

int main()
{
  int u = nondet_int();
  int v = nondet_int();
  int w = nondet_int();
  D<int, int, int> d(u, v, w); // partial spec; forwards Triple(h, t...), t=<int,int>
  __CPROVER_assert(static_cast<Triple &>(d).x == u, "leading arg forwarded");
  __CPROVER_assert(static_cast<Triple &>(d).z == w, "trailing pack last element forwarded");
  __CPROVER_assert(static_cast<Triple &>(d).z == u, "WRONG must FAIL");
  return 0;
}
