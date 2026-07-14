// N5008 [expr.prim.fold]/3: a unary fold over an EMPTY pack yields the
// operator's identity -- `true` for &&, `false` for ||, `void()` for the
// comma operator (any other operator with an empty pack is ill-formed).
// g++ and clang++ accept and run this (assert holds).
//
// KNOWNBUG: instantiating a function template with an EMPTY parameter pack
// whose body is a fold expression loses the body entirely ("no body for
// callee empty_and<>()"), so the call returns a nondeterministic value
// instead of the fold identity.  Distinct from the (fixed) one-element case:
// N == 0 takes the pack-removal path of the function-parameter-pack
// expansion, which does not rewrite the fold node to its identity value.
// Flip to CORE once the empty fold yields its identity.

extern "C" void __CPROVER_assert(int, const char *);

template<typename... U>
bool empty_and(U... u)
{
  return (u && ...);
}

template<typename... U>
bool empty_or(U... u)
{
  return (u || ...);
}

int main()
{
  __CPROVER_assert(empty_and() == true, "empty && fold yields true");
  __CPROVER_assert(empty_or() == false, "empty || fold yields false");
  return 0;
}
