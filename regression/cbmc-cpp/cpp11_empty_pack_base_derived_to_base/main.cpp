// N5008 [temp.variadic]/7: "when N is zero, the instantiation of the expansion
// produces an empty list".  A base-specifier whose template argument is a pack
// expansion `_Tail...` over an empty pack therefore collapses to `Empty<>`; the
// base remains a valid (empty) base of the instantiated class.
//
// This mirrors libstdc++'s tuple layout, where
// `_Tuple_impl<__i, _Head, _Tail...>` derives from both a recursive base
// (`_Tuple_impl<__i+1, _Tail...>`, here `Empty<_Tail...>`) and a
// `_Head_base<__i, _Head>` (here `Head_base`).  `Impl<0, int>::_M_head` then
// performs a derived-to-base call `_Base::_M_head(__t)` that converts the
// derived `Impl&` to its sibling base `Head_base&`.
//
// Regression: instantiating `Impl<0, int>` left the empty pack expansion
// `Empty<_Tail...>` unsubstituted (an empty pack has no pack_args_map entry,
// only pack_size_map == 0).  Resolving that malformed base threw, which took
// down the *whole* base list -- so `Head_base` was no longer a base and the
// `Impl& -> Head_base&` argument conversion failed ("found no match for
// _M_head"); the call was dropped and the function returned a nondet/NULL
// reference.  Now fixed: empty pack expansions are dropped from base-specifier
// argument lists during instantiation, leaving `Empty<>` and keeping the
// sibling base.
//
// Assertion 1 must SUCCEED; assertion 2 (a wrong value) must FAIL, proving the
// pass is non-vacuous (the body and its assertions are not silently dropped).

template <unsigned long __i, typename _Head>
struct Head_base
{
  _Head _M_head_impl;
  static _Head &_M_head(Head_base &__b) { return __b._M_head_impl; }
};

template <typename... _E>
struct Empty
{
};

template <unsigned long __i, typename _Head, typename... _Tail>
struct Impl : Empty<_Tail...>, Head_base<__i, _Head>
{
  typedef Head_base<__i, _Head> _Base;
  static _Head &_M_head(Impl &__t) { return _Base::_M_head(__t); }
};

int main()
{
  Impl<0, int> x;
  Impl<0, int>::_M_head(x) = 42;
  int a = Impl<0, int>::_M_head(x);
  __CPROVER_assert(a == 42, "empty-pack base keeps sibling derived-to-base");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}
