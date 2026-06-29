// N5008 [temp.variadic]/5, [temp.deduct.call]: this is the remaining layer of
// libstdc++'s `std::function<R(A...)>` converting-constructor constraint that
// is NOT yet handled.  `__invoke_result` is defined in terms of the variadic
// helper `std::__invoke`:
//
//   __invoke_result<F, A...>::type
//     = decltype(std::__invoke(declval<F>(), declval<A>()...));
//
// so after the call-argument pack `declval<A>()...` is expanded (which now
// works -- see cpp11_decltype_pack_nested_trait_ctor), the resulting call is
// to a VARIADIC FUNCTION TEMPLATE (`invoke_fn` below) whose own parameter pack
// must be deduced from the two-or-more expanded arguments, and whose trailing
// return type `decltype(f(args...))` must then be expanded -- all inside an
// unevaluated operand during the constructor's SFINAE.  That nested
// function-template pack deduction is not performed for a two-or-more-element
// pack, the constraint fails to elaborate, overload resolution reports "found
// no match", and the construction passes vacuously (unsound).  A single-element
// pack works.
//
// This is the precise remaining blocker for constructing a multi-argument
// std::function (and hence for the dog-food make_bvrep failures).
//
// KNOWNBUG; flip to CORE once a variadic function template's parameter pack is
// deduced from a two-or-more-argument call appearing in an unevaluated operand
// during constructor SFINAE.  Header-free and non-vacuous (assertion 2 must
// FAIL).

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
T &&declval();

template <class F, class... Args>
auto invoke_fn(F &&f, Args &&... a)
  -> decltype(static_cast<F &&>(f)(static_cast<Args &&>(a)...));

template <class F, class... A>
struct invoke_result
{
  using type = decltype(invoke_fn(declval<F>(), declval<A>()...));
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
  __CPROVER_assert(g.tag == 7, "variadic-invoke two-arg-pack constructor");
  __CPROVER_assert(g.tag == 0, "WRONG must FAIL");
  return 0;
}
