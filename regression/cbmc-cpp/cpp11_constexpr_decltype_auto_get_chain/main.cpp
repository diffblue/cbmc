// N5008 [dcl.spec.auto] + [temp.point]/1 + [temp.inst]/5: a `constexpr`
// function template with a *deduced* return type (`decltype(auto)`) that
// forwards to another `constexpr` function template with a derived-to-base
// pack parameter -- the libstdc++ `std::get` -> `std::__get_helper` ->
// `_Tuple_impl::_M_head` shape.
//
// `get<0>(t)` (deduced return type) forwards to `helper<0>(t)`, which takes
// `TI<_I, _H, _T...>&` and is reached by a [temp.deduct.call]/4.3
// derived-to-base conversion from `Tup<int>` (base `TI<0, int>`, `_T` empty).
//
// Regression: a constexpr specialization reached for an ordinary run-time call
// is deferred to the clean method-body drain (so the derived-to-base pack call
// resolves) -- but a function whose return type must be *deduced*
// (`auto`/`decltype(auto)`) must still be converted eagerly so the return type
// is known before its call sites.  Both conditions are needed: deferring the
// auto-return wrapper would leave its return type undeduced and the call
// unbindable; eagerly converting the non-auto inner `helper` would drop its
// derived-to-base pack call.  `get` (deduced) is converted eagerly and binds to
// the inner `helper`'s declared `_H&` return type, while `helper` (explicit
// return) is deferred and its body converted cleanly.
//
// Assertion 1 SUCCEEDs; assertion 2 (a wrong value) FAILs, proving non-vacuity.

template <unsigned long, typename _H>
struct HB
{
  _H v;
  static _H &mh(HB &b) { return b.v; }
};

template <unsigned long, typename...>
struct TI
{
};

template <unsigned long _I, typename _H, typename... _T>
struct TI<_I, _H, _T...> : TI<_I + 1, _T...>, HB<_I, _H>
{
  typedef HB<_I, _H> _B;
  static _H &mh(TI &t) { return _B::mh(t); }
};

template <typename... _E>
struct Tup : TI<0, _E...>
{
};

template <unsigned long _I, typename _H, typename... _T>
constexpr _H &helper(TI<_I, _H, _T...> &t)
{
  return TI<_I, _H, _T...>::mh(t);
}

template <unsigned long _I, typename... _E>
constexpr decltype(auto) get(Tup<_E...> &t)
{
  return helper<_I>(t);
}

int main()
{
  Tup<int> t;
  get<0>(t) = 42;
  int a = get<0>(t);
  __CPROVER_assert(a == 42, "constexpr decltype(auto) get chain");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}
