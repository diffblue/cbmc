// N5008 [temp.variadic]/5, [temp.deduct]/8, [over.ics.user]: a converting
// constructor whose viability is SFINAE-constrained through a NESTED trait
// whose member type is a `decltype` containing a call-argument pack expansion
// over the enclosing class parameter pack -- the shape of libstdc++'s
// `__invoke_result<F, A...>::type =
//   decltype(declval<F>()(declval<A>()...))` used to constrain
// `std::function<R(A...)>`'s converting constructor.  The call-argument pack
// expansion must be expanded into one argument per deduced element when the
// trait is instantiated, for a two-or-more-element pack.
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// must FAIL, so a vacuous "found no match" regression is caught.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class F, class... A>
struct invoke_result
{
  using type = decltype(declval<F>()(declval<A>()...));
};

template <class>
struct Fn;

template <class R, class... A>
struct Fn<R(A...)>
{
  int tag;
  template <class F, class = typename invoke_result<F &, A...>::type>
  Fn(F) : tag(7)
  {
  }
};

int main()
{
  Fn<bool(bool, bool)> g = [](bool p, bool q) { return p && q; };
  __CPROVER_assert(g.tag == 7, "nested-trait two-arg-pack constructor selected");
  __CPROVER_assert(g.tag == 0, "WRONG must FAIL");
  return 0;
}
