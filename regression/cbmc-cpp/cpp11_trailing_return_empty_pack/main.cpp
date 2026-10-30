// N5008 [temp.variadic]/5,7: a pack expansion whose pack expands to ZERO
// elements produces an empty list.  A variadic forwarding helper whose
// trailing-return type is a `decltype` containing a function-call pack
// expansion --
//   auto invk(F f, Args... a) -> decltype(f(a...));
// -- deduced with an EMPTY pack (called with only the callable) must expand
// `f(a...)` to `f()` and resolve to the call's result type.
//
// Now handled: for an empty deduced pack the pack parameter is never processed
// during deduction (the argument list is exhausted before the pack), so it
// kept only its build_unassigned placeholder and was recorded nowhere as empty.
// guess_function_template_args now records such an unbound trailing pack with
// size 0, so expand_call_argument_packs collapses the trailing-return `a...` to
// zero arguments and `decltype(invk(...))` resolves.  This applies to both the
// plain `f(a...)` and the forwarding-cast `static_cast<Args&&>(a)...` forms (the
// non-empty cases of which are handled by cpp11_trailing_return_plain_pack and
// cpp11_trailing_return_fwd_pack).
//
// Header-free and non-vacuous (assertion 2 must FAIL).

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
