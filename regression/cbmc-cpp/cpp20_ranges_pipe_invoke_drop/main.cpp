// cvise-reduced (83k -> 236 lines, header-free) from the libc++
// <ranges> views::take driver: with the hidden-friend operator|
// root FIXED (cpp20_hidden_friend_operator_template), the pipe
// `arr | views::take(3)` still drops main -- the failure sits in the
// __invoke/__invokable_r/invoke_result_t chain instantiated for the
// range-adaptor closure ("conversion from 'signed int [1l]' to
// '<<type:auto>>'" at the range expression; every one of the 236
// lines is load-bearing, hand-written sub-shapes all pass).  The
// assert argument was folded to a truthy constant by the reduction;
// the desc pattern requires the ASSERTION LINE so a dropped main
// (vacuous SUCCESS) keeps failing this test.  clang++ + ASan/UBSan
// + valgrind run the program clean.
template <int __v> struct integral_constant {
  static const int value = __v;
};
template <class _Tp> struct enable_if {
  typedef _Tp type;
};
namespace std {
template <class _Tp>
constexpr bool is_lvalue_reference_v = __is_lvalue_reference(_Tp);
template <class _Tp> _Tp __declval(int);
template <class _Tp> decltype(__declval<_Tp>(0)) declval();
template <class _From, class _To>
constexpr bool is_convertible_v = __is_convertible(_From, _To);
template <class _From, class>
concept convertible_to = requires { _From(); };
template <bool, class _If, class> using __conditional_t = _If;
template <class _Dp, class _Bp>
concept derived_from = is_convertible_v<_Dp, _Bp>;
struct __apply_cv_impl {
  template <class _Up> using __apply = _Up;
};
template <class, class _Up> using __apply_cv_t = __apply_cv_impl::__apply<_Up>;
template <class _Fp, class... _Args>
decltype(_Fp()(declval<_Args>()...)) __invoke(_Fp __f, _Args &&...__args) {
  return __f(__args...);
}
template <class, class _Fp, class... _Args> struct __invokable_r {
  template <class _XFp, class... _XArgs>
  static decltype(__invoke(_XFp(), declval<_XArgs>()...)) __try_call(int);
  using _Result = decltype(__try_call<_Fp, _Args...>(0));
};
template <class _Fp, class... _Args>
struct __invoke_of
    : enable_if<typename __invokable_r<void, _Fp, _Args...>::_Result> {};
template <class _Fn, class... _Args>
using invoke_result_t = __invoke_of<_Fn, _Args...>::type;
template <class _Fn, class... _Args>
invoke_result_t<_Fn, _Args...> invoke(_Fn __f, _Args &&...__args) {
  return __invoke(__f, __args...);
}
template <class> using iter_difference_t = int;
template <class _Ip>
concept input_or_output_iterator = requires(_Ip __i) { __i; };
struct {
  template <class _Tp, int _Np> auto operator()(_Tp (&__t)[_Np]) { return __t; }
} begin;
template <class _Tp> using iterator_t = decltype(begin(declval<_Tp>()));
template <unsigned long...> struct __tuple_indices {};
template <class _IdxType, _IdxType... _Values> struct __integer_sequence {
  template <long> using __to_tuple_indices = __tuple_indices<_Values...>;
};
template <long _Ep, long _Sp>
using __make_indices_imp =
    __make_integer_seq<__integer_sequence, long,
                       _Ep - _Sp>::template __to_tuple_indices<_Sp>;
template <class _Tp, _Tp...> struct integer_sequence;
template <long... _Ip>
using index_sequence = integer_sequence<unsigned long, _Ip...>;
template <class _Tp, _Tp _Ep>
using __make_integer_sequence = __make_integer_seq<integer_sequence, _Tp, _Ep>;
template <class _Tp, _Tp _Np>
using make_integer_sequence = __make_integer_sequence<_Tp, _Np>;
template <long _Np>
using make_index_sequence = make_integer_sequence<unsigned long, _Np>;
template <class... _Tp>
using index_sequence_for = make_index_sequence<sizeof...(_Tp)>;
template <class...> class tuple;
template <int _Ep, long _Sp = 0> struct __make_tuple_indices {
  typedef __make_indices_imp<_Ep, _Sp> type;
};
template <class...> struct __tuple_types {};
template <long, class> struct tuple_element;
template <long _Ip, class... _Types>
struct tuple_element<_Ip, __tuple_types<_Types...>> {
  typedef __type_pack_element<_Ip, _Types...> type;
};
template <class> struct tuple_size;
template <class... _Tp>
struct tuple_size<tuple<_Tp...>> : integral_constant<sizeof...(_Tp)> {};
template <class, class> struct __make_tuple_types_flat;
template <template <class...> class _Tuple, class... _Types, long... _Idx>
struct __make_tuple_types_flat<_Tuple<_Types...>, __tuple_indices<_Idx...>> {
  template <class _Tp>
  using __apply_quals =
      __tuple_types<__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>...>;
};
template <class _Tp, long _Ep = tuple_size<_Tp>::value, long _Sp = 0>
struct __make_tuple_types {
  using type =
      __make_tuple_types_flat<_Tp, typename __make_tuple_indices<_Ep, _Sp>::
                                       type>::template __apply_quals<_Tp>;
};
template <long _Ip, class... _Tp> struct tuple_element<_Ip, tuple<_Tp...>> {
  typedef tuple_element<_Ip, __tuple_types<_Tp...>>::type type;
};
template <bool _Const, class _Tp>
using __maybe_const = __conditional_t<_Const, _Tp, _Tp>;
template <class _Hp> struct __tuple_leaf {
  _Hp __value_;
  _Hp get() { return __value_; }
};
template <class...> struct __tuple_impl;
template <long... _Indx, class... _Tp>
struct __tuple_impl<__tuple_indices<_Indx...>, _Tp...> : __tuple_leaf<_Tp>... {
  template <unsigned long... _Uf, class... _Tf, class... _Up>
  __tuple_impl(__tuple_indices<_Uf...>, __tuple_types<_Tf...>,
               __tuple_indices<>, __tuple_types<>, _Up... __u)
      : __tuple_leaf<_Tf>(__u)... {}
};
template <class... _Tp> struct tuple {
  __tuple_impl<typename __make_tuple_indices<sizeof...(_Tp)>::type, _Tp...>
      __base_;
  template <class... _Up>
  tuple(_Up... __u)
      : __base_(typename __make_tuple_indices<sizeof...(_Up)>::type(),
                typename __make_tuple_types<tuple>::type(),
                typename __make_tuple_indices<sizeof...(_Tp),
                                              sizeof...(_Up)>::type(),
                typename __make_tuple_types<tuple, sizeof...(_Tp),
                                            sizeof...(_Up)>::type(),
                __u...) {}
};
template <int _Ip, class... _Tp>
tuple_element<_Ip, tuple<_Tp...>>::type get(tuple<_Tp...> __t) {
  return static_cast<
             __tuple_leaf<typename tuple_element<_Ip, tuple<_Tp...>>::type>>(
             __t.__base_)
      .get();
}
template <class _Tp> constexpr long tuple_size_v = tuple_size<_Tp>::value;
template <class...> struct __perfect_forward_impl;
template <class _Op, long... _Idx, class... _BoundArgs>
struct __perfect_forward_impl<_Op, index_sequence<_Idx...>, _BoundArgs...> {
  tuple<_BoundArgs...> __bound_args_;
  template <class... _Args>
  __perfect_forward_impl(_Args... __bound_args)
      : __bound_args_(__bound_args...) {}
  template <class... _Args>
  auto operator()(_Args &&...__args)
      -> decltype(_Op()(get<_Idx>(__bound_args_)..., __args...)) {
    return _Op()(get<_Idx>(__bound_args_)..., __args...);
  }
};
template <class _Op, class... _Args>
using __perfect_forward =
    __perfect_forward_impl<_Op, index_sequence_for<_Args...>, _Args...>;
namespace ranges {
template <class> constexpr bool enable_view = requires { nullptr; };
template <class _Rp> using range_difference_t = iter_difference_t<_Rp>;
template <class _Tp>
concept view = enable_view<_Tp>;
template <class _Tp>
concept viewable_range = is_lvalue_reference_v<_Tp>;
} // namespace ranges
template <class> struct __range_adaptor_closure;
template <class _Fn>
struct __range_adaptor_closure_t : _Fn, __range_adaptor_closure<_Fn> {};
template <class _Tp>
concept _RangeAdaptorClosure = derived_from<_Tp, _Tp>;
template <class> struct __range_adaptor_closure {
  template <ranges::viewable_range _View, _RangeAdaptorClosure _Closure>
  friend auto operator|(_View &&__view, _Closure __closure) {
    return invoke(__closure, __view);
  }
};
namespace ranges::views {
template <viewable_range _Range> using all_t = decltype(declval<_Range>());
}
template <long _NBound, class = make_index_sequence<_NBound>>
struct __bind_back_op;
template <long _NBound, long... _Ip>
struct __bind_back_op<_NBound, index_sequence<_Ip...>> {
  template <class _Fn, class _BoundArgs, class... _Args>
  auto operator()(_Fn __f, _BoundArgs __bound_args, _Args &&...__args)
      -> decltype(invoke(__f, __args..., get<_Ip>(__bound_args)...)) {
    return invoke(__f, __args..., get<_Ip>(__bound_args)...);
  }
};
template <class _Fn, class _BoundArgs>
struct __bind_back_t
    : __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>, _Fn,
                        _BoundArgs> {
  using __perfect_forward<__bind_back_op<tuple_size_v<_BoundArgs>>, _Fn,
                          _BoundArgs>::__perfect_forward;
};
template <class _Fn, class... _Args> auto __bind_back(_Fn __f, _Args...) {
  return __bind_back_t<_Fn, tuple<_Args...>>(__f, 0);
}
template <input_or_output_iterator _Iter> struct counted_iterator {
  counted_iterator(_Iter __iter, iter_difference_t<_Iter>)
      : __current_(__iter) {}
  _Iter base() { return __current_; }
  auto operator*() { return __current_; }
  void operator++() {}
  _Iter __current_;
};
namespace ranges {
template <view _View> struct take_view {
  _View __base_;
  range_difference_t<_View> __count_;
  template <bool> class __sentinel;
  auto begin() { return counted_iterator(__base_, __count_); }
  auto end() { return __sentinel<true>{}; }
};
template <view _View>
template <bool _Const>
struct take_view<_View>::__sentinel {
  template <bool _OtherConst>
  using _Iter = counted_iterator<iterator_t<__maybe_const<_OtherConst, _View>>>;
  template <bool _OtherConst = _Const>
  friend bool operator==(_Iter<_OtherConst> __lhs, __sentinel) {
    return __lhs.base();
  }
};
template <class _Range>
take_view(_Range &&,
          range_difference_t<_Range>) -> take_view<views::all_t<_Range>>;
namespace views {
struct {
  template <class _Range, convertible_to<_Range> _Np>
  auto operator()(_Range &&__range, _Np __n) {
    return take_view(__range, __n);
  }
  auto operator()(int __n) {
    return __range_adaptor_closure_t(__bind_back(*this, __n));
  }
} take;
} // namespace views
} // namespace ranges
namespace views = ranges::views;
} // namespace std
int main() {
  int arr[]{3};
  for (auto x : arr | std::views::take(3))
    __CPROVER_assert(6, "ranges take");
}
