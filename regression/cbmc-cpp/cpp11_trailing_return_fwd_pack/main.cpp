// N5008 [temp.variadic]/5, [dcl.fct]/2 (trailing-return-type): a variadic
// function template whose TRAILING-RETURN type is a `decltype` containing a
// forwarding-reference pack expansion --
//   auto invk(F&& f, Args&&... a)
//     -> decltype(static_cast<F&&>(f)(static_cast<Args&&>(a)...));
// (the declaration of libstdc++'s variadic `std::__invoke`) -- must, when
// instantiated/deduced with a two-or-more-element pack, expand the pack in the
// return-type `decltype` and resolve to the call's result type.
//
// KNOWN BUG: the call-argument pack `static_cast<Args&&>(a)...` is expanded for
// a function *body* (see cpp11_forwarding_ref_pack_expansion) but not for a
// trailing-return `decltype` on a declaration-only function template, so the
// return type fails to resolve, the call `invk(...)` has no usable type, and a
// `decltype(invk(...))` type silently fails (the proof passes vacuously --
// unsound).  A single-element pack works.
//
// This is the next layer for multi-argument std::function: __invoke_result is
// `decltype(std::__invoke(declval<F>(), declval<Args>()...))`, and std::__invoke
// is exactly this declaration-only variadic forwarding helper.
//
// Header-free and non-vacuous (assertion 2 must FAIL).  Flip to CORE once
// trailing-return `decltype` forwarding-reference pack expansion is
// implemented.

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class F, class... Args>
auto invk(F &&f, Args &&... a)
  -> decltype(static_cast<F &&>(f)(static_cast<Args &&>(a)...));

struct C
{
  bool operator()(bool, bool) const;
};

int main()
{
  // decltype(invk(...)) should be `bool`; size a bool* and check it.
  decltype(invk(declval<C &>(), declval<bool>(), declval<bool>())) *p = 0;
  __CPROVER_assert(p == 0, "trailing-return decltype resolves");
  __CPROVER_assert(p != 0, "WRONG must FAIL");
  return 0;
}
