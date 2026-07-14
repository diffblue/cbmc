// N5008 [expr.prim.fold]/2: a fold expression over a ONE-element pack reduces
// to the single instance of its pattern (for a binary fold, one application of
// the operator against the init operand); with more elements the operator
// chain applies.  Fixed: the one-element case previously skipped the fold
// rewrite entirely (the general pack expansion only runs for N != 1), so the
// residual fold node reached the C type-checker's fallback and degraded to
// `true`.  All shapes below are runtime-verified against g++ and clang++.

extern "C" void __CPROVER_assert(int, const char *);

template<typename... U>
int last_of(U... u)
{
  return (u, ...);
}

template<typename... U>
int sum_r(U... u)
{
  return (u + ...);
}

template<typename... U>
int sum_l(U... u)
{
  return (... + u);
}

template<typename... U>
int sum_b(U... u)
{
  return (100 + ... + u);
}

template<typename... U>
bool all_of(U... u)
{
  return (u && ...);
}

int main()
{
  __CPROVER_assert(last_of(7) == 7, "one-element comma fold yields it");
  __CPROVER_assert(last_of(1, 2, 9) == 9, "multi-element comma fold yields last");
  __CPROVER_assert(sum_r(7) == 7, "one-element right fold");
  __CPROVER_assert(sum_l(7) == 7, "one-element left fold");
  __CPROVER_assert(sum_b(7) == 107, "one-element binary fold");
  __CPROVER_assert(sum_b(1, 2) == 103, "two-element binary fold");
  __CPROVER_assert(all_of(true), "one-element && fold true");
  __CPROVER_assert(!all_of(false), "one-element && fold false");
  return 0;
}
