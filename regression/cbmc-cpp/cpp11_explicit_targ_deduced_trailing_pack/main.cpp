// N5008 [temp.arg.explicit]/3 + [temp.deduct.call]/3: a function template called
// with an explicit leading template argument and a trailing template parameter
// pack deduced from the call arguments must instantiate with the pack bound to
// exactly the supplied trailing arguments.
//
// Here `invoke_r<int>(fp, 2, 3)` fixes R=int explicitly and deduces F (from fp)
// and the pack A (from 2, 3).  The correct instantiation is
// `invoke_r<int, int(*)(int,int), int, int>` with signature
// `int(int(*)(int,int), int&&, int&&)`.
//
// KNOWN BUG: with an explicit leading template argument AND a multi-element
// deduced trailing pack (>= 2 elements), the instantiated candidate is built
// with one EXTRA pack parameter (e.g. three `int&&` instead of two), so overload
// resolution (disambiguate_functions) rejects it as having the wrong arity.  The
// call then matches no candidate and -- because the only candidate is a function
// template -- resolution silently bails (the "all candidates are templates"
// SFINAE-tolerance path in cpp_typecheck_resolvet::resolve), discarding the
// enclosing statement, so the program verifies only VACUOUSLY.  A single-element
// deduced pack with an explicit leading argument already works.
//
// This is the function-template analogue of the class-template-partial-spec
// "pack after fixed arguments" gap (cpp11_partial_spec_pack_after_fixed) and is
// the root of multi-argument std::function's _M_invoke/__invoke_r dispatch
// (a partial-spec-class method body calling such a nested template).
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once the
// explicit-leading-arg + deduced-trailing-pack instantiation has the correct
// arity.

extern "C" void __CPROVER_assert(int, const char *);

template <class R, class F, class... A>
R invoke_r(F f, A &&... a)
{
  return f(static_cast<A &&>(a)...);
}

int add(int a, int b)
{
  return a + b;
}

int main()
{
  int (*fp)(int, int) = add;
  int r = invoke_r<int>(fp, 2, 3); // explicit R, deduce F + trailing pack A
  __CPROVER_assert(r == 5, "explicit-targ + deduced trailing pack instantiates");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}
