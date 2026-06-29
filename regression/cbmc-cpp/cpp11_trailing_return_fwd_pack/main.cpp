// N5008 [temp.variadic]/5, [dcl.fct]/2 (trailing-return-type): a variadic
// function template whose TRAILING-RETURN type is a `decltype` containing a
// forwarding-reference pack expansion --
//   auto invk(F&& f, Args&&... a)
//     -> decltype(static_cast<F&&>(f)(static_cast<Args&&>(a)...));
// (the declaration of libstdc++'s variadic `std::__invoke`) -- must, when
// instantiated/deduced with a two-or-more-element pack, expand the pack in the
// return-type `decltype` and resolve to the call's result type.
//
// Now handled: the call-argument pack `static_cast<Args&&>(a)...` is expanded
// in the trailing-return `decltype` of a declaration-only function template by
// expand_call_argument_packs (apply), which detects the type parameter pack
// even when it is nested inside a reference type (`Args&&`) and substitutes the
// i-th deduced element type per copy (reference-collapsing).  The deduced
// return type then resolves to the call's result type and propagates to the
// call expression.
//
// This is the layer multi-argument std::function needs: __invoke_result is
// `decltype(std::__invoke(declval<F>(), declval<Args>()...))`, and std::__invoke
// is exactly this declaration-only variadic forwarding helper (see
// cpp11_decltype_pack_variadic_invoke_ctor).
//
// Header-free and non-vacuous (assertion 2 must FAIL).

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
