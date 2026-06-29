// N5008 [temp.variadic]/5 + [temp.deduct]/8 ([over.ics.user]): a converting
// constructor whose viability is SFINAE-constrained by a `decltype` containing
// a pack expansion over a TWO-OR-MORE-element pack -- the shape of
// libstdc++'s `std::function<R(A...)>` converting constructor, constrained by
// `_Callable<F> = __is_invocable_r<R, F&, A...>` -- must be considered when the
// pack expands to two or more elements.  (Reducing `make_bvrep`'s dog-food
// failure: it is called with a lambda that captures a
// `std::function<bool(bool,bool)>`, and constructing any multi-argument
// `std::function<R(A,B,...)>` from a callable hits this.)
//
// KNOWN BUG: with a two-element pack `A`, the pack expansion
// `declval<A>()...` inside the constructor's `decltype` SFINAE is not handled,
// the constructor is dropped, overload resolution reports "found no match", and
// the construction silently fails (the proof then passes vacuously -- unsound).
// A one-element pack works.  Flip to CORE once multi-element pack expansion in
// a decltype/unevaluated SFINAE operand is implemented.
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// must FAIL.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class>
struct Fn;

template <class R, class... A>
struct Fn<R(A...)>
{
  int tag;
  template <class F, class = decltype(declval<F &>()(declval<A>()...))>
  Fn(F) : tag(7)
  {
  }
};

int main()
{
  Fn<bool(bool, bool)> g = [](bool p, bool q) { return p && q; }; // two-arg pack
  __CPROVER_assert(g.tag == 7, "two-arg-pack SFINAE constructor selected");
  __CPROVER_assert(g.tag == 0, "WRONG must FAIL");
  return 0;
}
