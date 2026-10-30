// N5008 [expr.prim.fold]/3: a unary fold over an EMPTY pack yields the
// operator's identity -- `true` for &&, `false` for || (any other operator
// with an empty pack is ill-formed); a binary fold `(init op ... op pack)`
// over an empty pack yields its init operand.  Fixed: the empty-pack
// instantiation removes the pack parameter before the fold-rewriting body
// expansion runs (which is keyed to the parameter), so residual fold nodes
// reached the C type-checker's fallback and the function body degraded --
// the calls returned nondeterministic values.  Now residual folds in an
// empty-pack instantiation are rewritten to their identities.
// Runtime-verified against g++ and clang++.

extern "C" void __CPROVER_assert(int, const char *);

template <typename... U>
bool empty_and(U... u)
{
  return (u && ...);
}

template <typename... U>
bool empty_or(U... u)
{
  return (u || ...);
}

template <typename... U>
int sum_b(U... u)
{
  return (100 + ... + u);
}

int main()
{
  __CPROVER_assert(empty_and() == true, "empty && fold yields true");
  __CPROVER_assert(empty_or() == false, "empty || fold yields false");
  __CPROVER_assert(sum_b() == 100, "empty binary fold yields the init operand");
  __CPROVER_assert(sum_b(7) == 107, "one-element binary fold still applies op");
  return 0;
}
