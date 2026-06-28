// N5008 [temp.spec.partial.match] / [temp.deduct.type]: a class template
// partial specialization whose last template argument is a pack expansion
// `T...` matches an instantiation with at least as many arguments as the
// specialization has non-pack parameters; the trailing arguments are deduced
// as the pack.  This is the matching that drives the recursive shape of
// libstdc++'s _Tuple_impl.
//
// Here the recursive partial specialization `Rec<I, H, T...>` must be selected
// (not the primary) for THREE or more type arguments so the recursion reaches
// depth 2.  KNOWN BUG: for N>=2 trailing-pack elements the partial spec is
// skipped (the matcher requires an exact argument-count match), the primary is
// chosen, the recursion stops, and `main` is truncated -- a vacuous proof.
// Flip to CORE once trailing-pack partial-spec matching is implemented.
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// must FAIL, so a truncated/vacuous proof cannot pass.

extern "C" void __CPROVER_assert(int, const char *);

template <unsigned long, typename...>
struct Rec;

template <unsigned long I>
struct Rec<I>
{
  int sentinel;
};

template <unsigned long I, typename H, typename... T>
struct Rec<I, H, T...> : Rec<I + 1, T...>
{
  int depth = (int)I;
};

int main()
{
  Rec<0, int, int, int> r;
  __CPROVER_assert(static_cast<Rec<2, int> &>(r).depth == 2, "recursion reached depth 2");
  __CPROVER_assert(static_cast<Rec<2, int> &>(r).depth == 9, "WRONG must FAIL");
  return 0;
}
