// N5008 [dcl.ref]/1: a reference type cannot be cv-qualified.  However, GCC and
// Clang provide a language extension whereby a reference may carry a
// restrict-qualifier (`T & __restrict`), used as an aliasing hint.  CBMC aims
// to support gcc/clang extensions, and libstdc++ relies on this one: the
// declaration of `__cxxabiv1::__class_type_info::__do_upcast` in <cxxabi.h> has
// a `__upcast_result& __restrict __result` parameter, so any translation unit
// including <typeinfo> (transitively, most of the standard library) fails to
// parse without it.
//
// CBMC's C++ parser accepted `__restrict` after `*` (pointer) but not after `&`
// or `&&` (reference), reporting "parse error before ...".  Note that
// `const`/`volatile` on a reference remain ill-formed per [dcl.ref]/1 and are
// intentionally still rejected; only the `__restrict` extension is accepted.
//
// Non-vacuous: assertion.2 must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

struct R
{
  int v;
};

// __restrict-qualified lvalue reference parameter.
int use_lref(const R &__restrict r)
{
  return r.v;
}

// __restrict-qualified rvalue reference parameter.
int use_rref(R &&__restrict r)
{
  return r.v;
}

int main()
{
  R a{7};
  int x = use_lref(a);
  int y = use_rref(R{5});
  __CPROVER_assert(
    x == 7 && y == 5, "restrict-qualified reference params work");
  __CPROVER_assert(!(x == 7 && y == 5), "WRONG must FAIL");
  return 0;
}
