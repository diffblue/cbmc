// N5008 [temp.variadic]/5, [dcl.fct]/2 (trailing-return-type): a variadic
// function template whose trailing-return type is a `decltype` containing a
// *plain* (by-value, non-cast) function-call pack expansion --
//   auto invk(F f, Args... a) -> decltype(f(a...));
// -- must, when deduced with a two-or-more-element pack, expand the value
// parameter pack `a...` in the return-type `decltype` and resolve to the
// call's result type.
//
// KNOWN BUG: the forwarding-cast form `static_cast<Args&&>(a)...` is handled
// (see cpp11_trailing_return_fwd_pack) because its pattern references the TYPE
// parameter pack `Args`, which expand_call_argument_packs expands; but the
// plain `a...` pattern references only the VALUE parameter pack `a` (no type
// pack), so it is not expanded and `decltype(invk(...))` silently fails (the
// proof passes vacuously -- unsound).  A single-element pack works.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once a
// value parameter pack with no type-pack reference is expanded in a
// trailing-return decltype.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class F, class... Args>
auto invk(F f, Args... a) -> decltype(f(a...));

struct C
{
  bool operator()(bool, bool) const;
};

int main()
{
  decltype(invk(declval<C>(), declval<bool>(), declval<bool>())) *p = 0;
  __CPROVER_assert(p == 0, "plain value-pack decltype resolves");
  __CPROVER_assert(p != 0, "WRONG must FAIL");
  return 0;
}
