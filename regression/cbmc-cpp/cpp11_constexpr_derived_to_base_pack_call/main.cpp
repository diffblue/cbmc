// N5008 [temp.deduct.call]/4.3 + [dcl.constexpr]: a `constexpr` function
// template `helper(TI<_I, _H, _T...>&)` is called with a derived-class argument
// `Tup<int>` (whose base is `TI<0, int>`), deducing `_I = 0`, `_H = int`, `_T`
// empty.  `helper` returns `TI<0,int>::mh(t)`, which forwards to its sibling
// base `HB<0,int>::mh` via a derived-to-base conversion.
//
// Regression: a `constexpr` callee is marked is_macro and used to be converted
// *eagerly* and inline at the reference (so a constexpr value can be folded),
// rather than via the deferred method-body queue used for ordinary function
// templates.  In that nested/eager context the derived-to-base pack call was
// not built and the callee's body (and its sub-instantiations such as
// `TI::mh`) were dropped, so `helper<0>(t)` returned a nondet reference.  Per
// N5008 [temp.point]/1 and [temp.inst]/5 a constexpr specialization is now
// converted eagerly only when instantiated from a constant-expression context
// (where its value must be folded now); reached for an ordinary run-time call
// it is deferred to the clean method-body drain like any function, so the
// derived-to-base pack call resolves.  std::__get_helper / _Tuple_impl::_M_head
// are constexpr, so this is on the path to real std::get<0>.
//
// Assertion 1 SUCCEEDs and assertion 2 (a wrong value) FAILs, proving
// non-vacuity (the body and its assertions are not silently dropped).

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

int main()
{
  Tup<int> t;
  helper<0>(t) = 42;
  int a = helper<0>(t);
  __CPROVER_assert(a == 42, "constexpr derived-to-base pack call");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}
