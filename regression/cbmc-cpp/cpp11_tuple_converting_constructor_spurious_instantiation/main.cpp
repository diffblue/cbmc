// Reduced (cvise) from libc++ 18's
// std::is_constructible_v<std::tuple<at, std::tuple<int>>,
//                         const std::tuple<at, std::tuple<int>> &,
//                         std::tuple<int> &&>
// (the remaining layer of cpp20_libcxx_header_drops/test_bind_back).
// Checking the constraints of tuple's constructors must not instantiate the
// body of __tuple_impl's converting constructor: N5008 [temp.inst]/11 forbids
// instantiating a function body that is not needed, and clang never does
// (the initializer __tuple_leaf<_Tp>(forward) would be ill-formed).  CBMC
// instantiates it and drops it.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool, class _Tp = void>
using __enable_if_t = _Tp;
template <int __v>
struct integral_constant
{
  static const int value = __v;
};
template <class>
void forward();
template <class _Tp, class... _Args>
struct is_constructible : integral_constant<__is_constructible(_Tp, _Args...)>
{
};
template <class _Tp, class... _Args>
constexpr bool is_constructible_v = __is_constructible(_Tp, _Args...);
template <class...>
using __expand_to_true = integral_constant<true>;
__expand_to_true<> __trans_tmp_1;
template <class...>
using _And = decltype(__trans_tmp_1);
template <class...>
class tuple;
template <long...>
struct __tuple_indices;
template <int _Ep, long _Sp = 0>
struct __make_tuple_indices
{
  typedef __tuple_indices<> type;
};
template <class>
struct __make_tuple_types
{
  typedef int type;
};
template <class>
struct __tuple_like_ext;
template <class... _Tp>
struct __tuple_like_ext<tuple<_Tp...>> : integral_constant<true>
{
};
struct __tuple_sfinae_base
{
  template <class _FromArgs, class>
  using __constructible = decltype(is_constructible(_FromArgs{}));
};
template <class _Tp, class, bool = __tuple_like_ext<_Tp>::value>
struct __tuple_constructible;
template <class _Tp, class _Up>
struct __tuple_constructible<_Tp, _Up, true>
  : __tuple_sfinae_base::__constructible<
      typename __make_tuple_types<_Tp>::type,
      typename __make_tuple_types<_Up>::type>
{
};
template <class>
struct _Lazy;
template <class>
struct _Not;
template <class>
struct __tuple_leaf
{
};
template <class...>
struct __tuple_impl;
template <long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...> : __tuple_leaf<_Tp>...
{
  template <
    class _Tuple,
    class = __enable_if_t<__tuple_constructible<_Tuple, tuple<>>::value>>
  __tuple_impl(_Tuple) : __tuple_leaf<_Tp>(forward)...
  {
  }
};
template <class... _Tp>
struct tuple
{
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type, _Tp...>
    __base_;
  template <class _OtherTuple, class = _OtherTuple>
  struct _EnableCtorFromUTypesTuple;
  template <class _OtherTuple, class... _Up>
  struct _EnableCtorFromUTypesTuple<_OtherTuple, tuple<_Up...>>
    : _And<_Lazy<_Not<is_constructible<_Tp, _OtherTuple>>...>>
  {
  };
  template <__enable_if_t<_And<>::value, int> = 0>
  constexpr tuple(tuple<> &&__t) : __base_(__t)
  {
  }
  template <
    __enable_if_t<_And<_EnableCtorFromUTypesTuple<tuple<>>>::value, int> = 0>
  tuple();
};
static_assert(!is_constructible_v<tuple<tuple<int>>, tuple<>, tuple<>>);

int main()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
