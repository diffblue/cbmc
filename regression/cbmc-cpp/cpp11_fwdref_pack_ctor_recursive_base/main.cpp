// N5008 [temp.deduct.call]/3 + [dcl.init]/17 + [temp.variadic]/4-5: a variadic
// constructor taking a forwarding-reference parameter pack `_U&&... __e` deduces
// each `_U` independently and forwards each element into a recursive base's
// constructor.  This is exactly libstdc++ std::tuple's constructor
// (`tuple(_UElements&&...) : _Inherited(std::forward<_UElements>(__e)...)`,
// with `_Tuple_impl<_Idx,_Head,_Tail...> : _Tuple_impl<_Idx+1,_Tail...>`),
// used for THREE or more elements (two-element tuples use a non-variadic
// specialization, which is why cpp17_tuple_basic's make_tuple(1,2.0,'a') is the
// first case to hit this).
//
// FIXED (was KNOWNBUG): with a forwarding-reference parameter pack whose elements
// are of DISTINCT types (`tuple<int,double>` -> `_U = {int,double}`), CBMC
// stores the wrong element values (get<0> reads a value != the constructor
// argument).  A same-typed pack (`tuple<int,int>`) is stored correctly, and a
// by-VALUE variadic constructor pack (`_U... __e`) is stored correctly at every
// arity (cpp17_tuple_get_two_pack_ctor_3elem, CORE), so the defect is specific
// to a forwarding-reference (`_U&&`) parameter pack forwarded through recursive
// base construction with heterogeneous element types.  g++/clang++ store 1.
//
// This is the forwarding-reference core of libstdc++ std::tuple's constructor
// (used for 3+ elements); fixed by substituting the parallel type pack per
// element in the member-initializer expansion.

extern "C" void __CPROVER_assert(int, const char *);

template <unsigned long, class _Head>
struct _Head_base
{
  _Head _M_head_impl;
  template <class _UHead>
  _Head_base(_UHead &&__h) : _M_head_impl(static_cast<_UHead &&>(__h))
  {
  }
};
template <unsigned long, class...>
struct _Tuple_impl;
template <unsigned long _Idx, class _Head, class... _Tail>
struct _Tuple_impl<_Idx, _Head, _Tail...> : _Tuple_impl<_Idx + 1, _Tail...>,
                                            _Head_base<_Idx, _Head>
{
  template <class _UHead, class... _UTail>
  _Tuple_impl(_UHead &&__h, _UTail &&... __t)
    : _Tuple_impl<_Idx + 1, _Tail...>(static_cast<_UTail &&>(__t)...),
      _Head_base<_Idx, _Head>(static_cast<_UHead &&>(__h))
  {
  }
};
template <unsigned long _Idx, class _Head>
struct _Tuple_impl<_Idx, _Head> : _Head_base<_Idx, _Head>
{
  template <class _UHead>
  _Tuple_impl(_UHead &&__h) : _Head_base<_Idx, _Head>(static_cast<_UHead &&>(__h))
  {
  }
};
template <class... _E>
struct tuple : _Tuple_impl<0, _E...>
{
  template <class... _U>
  tuple(_U &&... __e) : _Tuple_impl<0, _E...>(static_cast<_U &&>(__e)...)
  {
  }
};
template <unsigned long __i, class _Head, class... _Tail>
_Head __get_helper(_Tuple_impl<__i, _Head, _Tail...> &__t)
{
  return static_cast<_Head_base<__i, _Head> &>(__t)._M_head_impl;
}
template <int __i, class... _E>
auto get(tuple<_E...> &__t)
{
  return __get_helper<__i>(__t);
}

int main()
{
  tuple<int, double> t(11, 22.0);
  __CPROVER_assert(get<0>(t) == 11, "get<0> keeps its int value under forwarding");
  __CPROVER_assert(
    get<1>(t) == 22.0, "get<1> keeps its double value under forwarding");
  return 0;
}
