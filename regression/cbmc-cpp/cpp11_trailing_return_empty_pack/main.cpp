// N5008 [temp.variadic]/5,7: a pack expansion whose pack expands to ZERO
// elements produces an empty list.  A variadic forwarding helper whose
// trailing-return type is a `decltype` containing a function-call pack
// expansion --
//   auto invk(F f, Args... a) -> decltype(f(a...));
// -- deduced with an EMPTY pack (called with only the callable) must expand
// `f(a...)` to `f()` and resolve to the call's result type.
//
// KNOWN BUG: for an empty deduced pack the pack parameter is never processed
// during deduction (the argument list is exhausted before the pack), so the
// pack is recorded nowhere; expand_call_argument_packs cannot tell that the
// trailing-return `a...` should collapse to zero arguments, the return type
// fails to resolve, and `decltype(invk(...))` silently fails (vacuous).  This
// empty-pack case affects both the plain `f(a...)` and the forwarding-cast
// `static_cast<Args&&>(a)...` forms (the non-empty cases of which are handled
// by cpp11_trailing_return_plain_pack and cpp11_trailing_return_fwd_pack).
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once an
// empty deduced parameter pack is recorded so its trailing-return decltype
// pack expansion collapses to zero arguments.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class F, class... Args>
auto invk(F f, Args... a) -> decltype(f(a...));

struct C
{
  bool operator()() const;
};

int main()
{
  decltype(invk(declval<C>())) *p = 0;
  __CPROVER_assert(p == 0, "empty-pack decltype resolves");
  __CPROVER_assert(p != 0, "WRONG must FAIL");
  return 0;
}
