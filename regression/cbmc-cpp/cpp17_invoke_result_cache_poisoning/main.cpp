template <int __v>
struct integral_constant
{
  static constexpr int value = __v;
};
template <bool __v>
using __bool_constant = integral_constant<__v>;
template <bool, typename _Tp>
using __enable_if_t = _Tp;
template <typename>
struct __and_;
template <typename>
struct __not_ : __bool_constant<!bool()>
{
};
template <typename _Tp, typename _Up = _Tp>
_Up __declval(int);
template <typename _Tp>
auto declval() -> decltype(__declval<_Tp>(0));
template <typename _Tp>
struct __success_type
{
  typedef _Tp type;
};
template <bool, bool, typename...>
struct __result_of_impl;
struct __result_of_other_impl
{
  template <typename _Fn, typename... _Args>
  static __success_type<decltype(declval<_Fn>()(_Args()...))> _S_test(int);
};
template <typename _Functor, typename... _ArgTypes>
struct __result_of_impl<false, false, _Functor, _ArgTypes...>
  : __result_of_other_impl
{
  typedef decltype(_S_test<_Functor, _ArgTypes...>(0)) type;
};
template <typename _Functor, typename... _ArgTypes>
struct __invoke_result : __result_of_impl<
                           integral_constant<false>::value,
                           integral_constant<false>::value,
                           _Functor,
                           _ArgTypes...>::type
{
};
template <typename _Result>
struct __is_invocable_impl
{
  using _Res_t = typename _Result::type;
  static _Res_t _S_get();
  template <
    typename _Tp,
    typename = decltype(_Tp(_S_get())),
    bool _Dangle = __reference_converts_from_temporary(_Tp, _Res_t)>
  static __bool_constant<_Dangle> _S_test(int);
  using type = decltype(_S_test<int>(1));
};
template <typename>
struct __call_is_nothrow;
template <typename _Fn, typename... _Args>
using __call_is_nothrow_ = __call_is_nothrow<__invoke_result<_Fn, _Args...>>;
struct hash
{
  void operator()(int);
};
template <typename, typename... _Args>
struct __is_nothrow_invocable : __and_<__call_is_nothrow_<hash, _Args...>>
{
};
struct instructiont;
struct _List_iterator
{
  instructiont operator*();
  void operator++();
  friend bool operator!=(_List_iterator, _List_iterator);
  _List_iterator begin();
  _List_iterator end();
} instructions;
template <typename _Tp, typename _Hash>
using __cache_default = __not_<__and_<__is_nothrow_invocable<_Hash, _Tp>>>;
template <bool>
using __umap_traits = int;
template <
  typename _Key,
  typename,
  typename _Hash,
  typename = __umap_traits<__cache_default<_Key, _Hash>::value>>
using __umap_hashtable = int;
__umap_hashtable<int, int, int> _Hashtableunordered_map;
template <typename>
class function;
template <typename _Cond, typename _Tp = void>
using _Requires = __enable_if_t<_Cond::value, _Tp>;
template <typename _Res, typename... _ArgTypes>
struct function<_Res(_ArgTypes...)>
{
  template <
    typename _Func,
    typename _DFunc = _Func,
    typename _Res2 = __invoke_result<_DFunc, _ArgTypes...>>
  struct _Callable : __is_invocable_impl<_Res2>::type
  {
  };
  template <typename _Functor, typename = _Requires<_Callable<_Functor>>>
  function(_Functor)
  {
  }
};
struct instructiont
{
  void transform(function<int(int)>);
};
void adjust_float_expressions()
{
  for(auto i : instructions)
    i.transform([](int) -> int {});
}
