// N5008 [temp.spec.partial.match] / [temp.deduct.type]: a class template
// partial specialization whose last template argument is a pack expansion
// `Rest...` matches an instantiation with at least as many arguments as the
// specialization has non-pack parameters; the leading arguments are deduced
// one-to-one and the trailing arguments are deduced as the pack.
//
// Here `Picker<First, Rest...>` must be selected over the primary for THREE
// type arguments (a two-element trailing pack), with `First` deduced to the
// first argument.  Previously the matcher required an exact argument-count
// match, so a two-or-more-element trailing pack made it skip the partial spec
// and pick the primary.
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// would hold only if the primary were (incorrectly) selected, so it must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

template <typename...>
struct Picker
{
  int n;
  Picker() : n(-1) {} // primary: sentinel
};

template <typename First, typename... Rest>
struct Picker<First, Rest...>
{
  int n;
  Picker() : n((int)sizeof(First)) {} // partial spec: size of the deduced First
};

int main()
{
  Picker<char, int, long> p; // 3 args => two-element trailing pack
  __CPROVER_assert(
    p.n == (int)sizeof(char), "trailing-pack partial spec selected, First=char");
  __CPROVER_assert(p.n == -1, "WRONG must FAIL (primary not selected)");
  return 0;
}
