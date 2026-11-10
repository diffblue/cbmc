// A requires-clause whose constraint is a concept TEMPLATE-ID with
// more than one argument (`requires same_as<T, int>`).  N5008
// [temp.pre]/[temp.constr.decl]: the clause constrains the template;
// here it must make the constrained pick() overload viable only for
// int, so pick(0.0) selects the unconstrained overload.  CBMC's
// parser fails to store such a clause -- rConditionalExpr parses the
// `<` as less-than, the post-clause token whitelist then mismatches,
// and only a constraint COUNT is kept (parse.cpp requires-clause
// fallback) -- so the constraint is DROPPED and the constrained
// overload stays viable for every type (wrong code: pick(0.0)
// returns 1).  A SINGLE-argument concept constraint (`requires
// is_int<T>`) parses and works; only the multi-argument template-id
// is affected.  g++ and clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class U>
concept same_as = __is_same(T, U);

template <class T>
int pick(T v)
  requires same_as<T, int>
{
  return 1;
}
template <class T>
int pick(T v)
{
  return 2;
}

int main()
{
  __CPROVER_assert(pick(0) == 1, "constrained overload wins for int");
  __CPROVER_assert(pick(0.0) == 2, "unconstrained wins for double");
  return 0;
}
