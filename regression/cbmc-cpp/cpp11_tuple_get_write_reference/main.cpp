// N5008 [temp.deduct.call]/4.3, [class.member.lookup], [over.match.funcs]: a
// cvise-reduced, header-free model of the libstdc++ std::get<0> write path
// (std::get -> std::__get_helper -> _Tuple_impl::_M_head, where _M_head is a
// static member inherited from a _Head_base base).  Well-defined under a
// conforming compiler: get<0>(t)=42 then reading get<0>(t) yields 42 (verified
// with g++).
//
// KNOWNBUG: CBMC drops get<0>'s (constexpr) body, so get<0>(t) returns a nondet
// (NULL) reference and the write is lost.  Root cause (traced): get is constexpr
// and deferred to the method-body drain; converting its body instantiates
// __get_helper<0>, whose body resolves the inherited static call
// _Tuple_impl<0,int>::_M_head(__t) via a derived-to-base conversion of the
// by-value argument.  That resolution fails ("found no match for symbol
// '_M_head'") ONLY when the sibling SFINAE overload
// `__enable_if_t<__i >= sizeof...(_Types)> __get_helper(tuple<_Types...>)` is
// also present (removing it makes the program verify) -- the SFINAE overload's
// failed deduction perturbs the resolver state so the derived-to-base _M_head
// call no longer matches.  The thrown resolution failure is swallowed by the
// drain, leaving get<0> bodyless.
//
// Flip to CORE once get<0>'s body converts: assertion 1 (the write took effect)
// must SUCCEED and assertion 2 (a wrong value) must FAIL, proving non-vacuity.
template <bool, typename>
struct enable_if;
template <typename _Tp>
struct enable_if<true, _Tp>
{
  typedef _Tp type;
};
template <bool _Cond, typename _Tp = void>
using __enable_if_t = enable_if<_Cond, _Tp>::type;
template <unsigned long, typename>
struct tuple_element;
template <long __i, typename _Tp>
using __tuple_element_t = tuple_element<__i, _Tp>::type;
template <typename... _Types>
void __find_uniq_type_in_pack();
template <long, typename...>
struct _Nth_type;
template <typename _Tp0, typename... _Rest>
struct _Nth_type<0, _Tp0, _Rest...>
{
  using type = _Tp0;
};
int _M_head_impl;
struct _Head_base
{
  static int &_M_head(_Head_base)
  {
    return _M_head_impl;
  }
};
template <unsigned long, typename...>
struct _Tuple_impl;
template <unsigned long _Idx, typename _Head>
struct _Tuple_impl<_Idx, _Head> : _Head_base
{
};
template <typename... _Elements>
struct tuple : _Tuple_impl<0, _Elements...>
{
};
template <unsigned long __i, typename... _Types>
struct tuple_element<__i, tuple<_Types...>>
{
  using type = _Nth_type<__i, _Types...>::type;
};
template <int __i, typename... _Tail>
int &__get_helper(_Tuple_impl<__i, int, _Tail...> __t)
{
  return _Tuple_impl<__i, int>::_M_head(__t);
}
template <int __i, typename... _Types>
__enable_if_t<__i >= sizeof...(_Types)> __get_helper(tuple<_Types...>);
template <int __i, typename... _Elements>
constexpr __tuple_element_t<__i, tuple<_Elements...>> &
get(tuple<_Elements...> __t)
{
  return __get_helper<__i>(__t);
}
int main()
{
  tuple<int> t;
  get<0>(t) = 42;
  int a = get<0>(t);
  __CPROVER_assert(a == 42, "tuple get write/read");
  __CPROVER_assert(a == 999, "WRONG (must FAIL)");
}
