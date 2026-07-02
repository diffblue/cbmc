// N5008 [temp.alias]/2 and [temp.deduct.type]: a template alias is replaced by
// its (one-step, fully resolved) underlying type; deducing template arguments
// against an alias-template parameter expands the alias exactly once and then
// matches the resolved type.
//
// A member alias template whose underlying type names a class template of the
// same unqualified base name -- as in libstdc++'s regex compiler, where
// `_Compiler<_TraitsT>` declares
//   template<bool I, bool C> using _BracketMatcher
//     = __detail::_BracketMatcher<_TraitsT, I, C>;
// -- used to send CBMC's argument deduction into unbounded recursion: after
// expanding the alias to `__detail::_BracketMatcher<...>`, the (qualified)
// expansion's base name was looked up unqualified, re-found the member alias,
// and re-expanded until the stack was exhausted.  The alias is now expanded
// only for an unqualified template-id, so the deduction terminates and binds
// the arguments correctly.
//
// This reproduces the shape with a plain member alias template used as a
// deduced function-template parameter.  assertion.1 verifies the arguments were
// deduced correctly (I=true, C=false); assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

namespace ns {
template <class T, bool I, bool C>
struct Matcher
{
};
} // namespace ns

template <class T>
struct Compiler
{
  // Member alias template whose underlying type has the same unqualified base
  // name ("Matcher") as the alias itself.
  template <bool I, bool C>
  using Matcher = ns::Matcher<T, I, C>;

  // Function template taking the alias as a (deduced) parameter.
  template <bool I, bool C>
  static int classify(Matcher<I, C>)
  {
    return (I ? 2 : 0) + (C ? 1 : 0);
  }

  static int run()
  {
    ns::Matcher<T, true, false> m;
    return classify(m); // deduce I = true, C = false  ->  2
  }
};

int main()
{
  int r = Compiler<char>::run();
  __CPROVER_assert(
    r == 2, "alias-template argument deduction yields I=true, C=false");
  __CPROVER_assert(r != 2, "WRONG must FAIL");
  return 0;
}
