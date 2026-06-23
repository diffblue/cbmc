// N5008 [temp.deduct.call]/4.3 + [dcl.constexpr]: a `constexpr` function
// template `helper(TI<_I, _H, _T...>&)` is called with a derived-class argument
// `Tup<int>` (whose base is `TI<0, int>`), deducing `_I = 0`, `_H = int`, `_T`
// empty.  `helper` returns `TI<0,int>::mh(t)`, which forwards to its sibling
// base `HB<0,int>::mh` via a derived-to-base conversion.
//
// KNOWNBUG: when the callee is `constexpr` it is converted *eagerly* and inline
// at the reference (so a constexpr value can be folded), rather than via the
// deferred method-body queue used for ordinary function templates.  In that
// nested/eager context the derived-to-base pack call is not built and the
// callee's body is dropped, so `helper<0>(t)` returns a nondet reference.  The
// non-constexpr form of this exact shape works (see
// cpp11_empty_pack_base_derived_to_base and
// cpp11_derived_to_base_pack_call_in_body); only the `constexpr` eager path is
// affected.  This is the next libstdc++-tuple layer: `std::__get_helper` /
// `_Tuple_impl::_M_head` are `constexpr`.
//
// Desired once fixed: assertion 1 SUCCEEDs and assertion 2 (a wrong value)
// FAILs, proving non-vacuity.  Currently the whole body is dropped and the
// assertions vanish (a vacuous "VERIFICATION SUCCESSFUL").

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
