// N5008 [expr.prim.fold]: a unary right fold `(u, ...)` over the comma
// operator with a one-element pack yields that element; with more elements it
// yields the last.  g++ and clang++ agree (runtime-checked).
//
// KNOWNBUG: for a ONE-element pack the fold is mis-expanded to `true` (the
// multi-element case works), so the returned value is wrong.  Discovered as a
// side-find while minimizing cpp17_ctor_template_cross_pack_constraint.
// Flip to CORE once the single-element comma fold expands to its operand.

extern "C" void __CPROVER_assert(int, const char *);

template<typename... Us>
int last_of(Us... u)
{
  return (u, ...);
}

int main()
{
  __CPROVER_assert(last_of(7) == 7, "one-element comma fold yields it");
  __CPROVER_assert(last_of(1, 2, 9) == 9, "multi-element comma fold yields last");
  return 0;
}
