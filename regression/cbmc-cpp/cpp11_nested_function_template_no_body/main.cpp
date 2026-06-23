// N5008 [temp.inst]/4, [temp.point]/1: an odr-used function-template
// specialization is implicitly instantiated, including its definition, so a
// call to it must reach a real body -- not a nondet "no body" stub.
//
// This is a cvise-reduced, header-free model of the libstdc++ std::get<0>
// chain (std::get -> std::__get_helper -> _Tuple_impl::_M_head).  It is
// well-defined and returns 42 under a conforming compiler (verified with g++).
// The scaffolding (the second SFINAE __get_helper overload, enable_if,
// _Nth_type, __tuple_element_t, __find_uniq_type_in_pack, and the by-value
// parameters) is needed to trigger the bug; hand-simplified variants do not
// reproduce it.
//
// KNOWNBUG: the called __get_helper<0> specialization is deferred to the
// method-body drain, but its body conversion throws and the body is dropped,
// leaving a bodyless function that returns a nondet reference (CBMC reports
// "no body for callee __get_helper<0>").
//
// Root cause (traced): __get_helper has a non-deduced trailing parameter pack
// `_Tail` that appears only in the body (`_Tuple_impl<__i, int, _Tail...>::
// _M_head`), so for `__get_helper<0>` it should be empty.  But this call is
// resolved from *within* get<0>'s body, and the deduction/instantiation gives
// __get_helper<0> a spurious extra template argument that bleeds from the
// enclosing get<0>'s element pack -- so `_Tail` is recorded with size 1
// (pack_size_map/pack_args_map) instead of 0.  Resolving the body's qualifier
// `_Tuple_impl<__i, int, _Tail...>` then tries to expand a phantom one-element
// `_Tail...` that has no bound element type, which throws; the deferred drain
// silently nil's the body.  (An earlier "struct member must not be of code
// type" symex invariant is a downstream symptom, not the cause.)
//
// Flip to CORE once __get_helper<0>'s _Tail is correctly empty and the body
// converts: assertion 1 must SUCCEED and assertion 2 (a wrong value) must FAIL,
// proving non-vacuity.

template <bool, typename> struct enable_if;
template <typename _Tp> struct enable_if<true, _Tp>
{
  typedef _Tp type;
};
template <bool _Cond, typename _Tp = void>
using __enable_if_t = enable_if<_Cond, _Tp>::type;
template <unsigned long, typename> struct tuple_element;
template <long __i, typename _Tp>
using __tuple_element_t = tuple_element<__i, _Tp>::type;
template <typename... _Types> void __find_uniq_type_in_pack();
template <long, typename...> struct _Nth_type;
template <typename _Tp0, typename... _Rest>
struct _Nth_type<0, _Tp0, _Rest...>
{
  using type = _Tp0;
};
int _M_head_impl;
struct _Head_base
{
  static int &_M_head(_Head_base) { return _M_head_impl; }
};
template <unsigned long, typename...> struct _Tuple_impl;
template <unsigned long _Idx, typename _Head>
struct _Tuple_impl<_Idx, _Head> : _Head_base
{
};
template <typename... _Elements> struct tuple : _Tuple_impl<0, _Elements...>
{
};
template <unsigned long __i, typename... _Types>
struct tuple_element<__i, tuple<_Types...>>
{
  using type = _Nth_type<__i, _Types...>::type;
};
template <int __i, typename... _Tail>
int &__get_helper(_Tuple_impl<__i, int> __t)
{
  return _Tuple_impl<__i, int, _Tail...>::_M_head(__t);
}
template <int __i, typename... _Types>
__enable_if_t<__i >= sizeof...(_Types)> __get_helper(tuple<_Types...>);
template <int __i, typename... _Elements>
__tuple_element_t<__i, tuple<_Elements...>> &get(tuple<_Elements...> __t)
{
  return __get_helper<__i>(__t);
}
int main()
{
  tuple<int> t;
  get<0>(t) = 42;
  int a = get<0>(t);
  __CPROVER_assert(a == 42, "nested template helper body");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
  return 0;
}
